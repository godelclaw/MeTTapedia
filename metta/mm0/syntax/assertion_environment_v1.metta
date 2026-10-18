; Ordered MM0 definition, axiom, and theorem declaration semantics.
;
; Definitions use the term namespace and signature, with their optional body
; and local dummy binders retained in source metadata. Axioms and theorems
; elaborate to assertion signatures; proofs are checked by the distinct .mmb
; transition system. Concrete .mm0 files remain runtime inputs.

(gslt-presentation-v1 MM0AssertionEnvironmentV1
  (signature
    (operator node 2)
    (operator pair 2)
    (operator some 1)
    (operator cons 2)
    (operator different 2)
    (operator MM0IdentifierScalarsV1 2)
    (operator MM0ListAppendV1 3)

    (operator MM0SourceStateV1 2)
    (operator MM0TextualEnvironmentV1 2)
    (operator MM0TermEntryV1 4)
    (operator MM0DeclarationEntriesConsV1 2)
    (operator MM0DeclarationLookupV1 3)
    (operator MM0TermSignatureLookupV1 3)
    (operator MM0MathTermTokenArityLookupV1 4)
    (operator MM0CheckAcceptedV1 1)
    (operator MM0CheckRefusedV1 1)
    (operator MM0ValidateExplicitBindersV1 7)
    (operator MM0BinderSequenceV1 3)
    (operator MM0RuntimeProvableExpressionElaborateV1 5)
    (operator MM0ExpressionAcceptedV1 2)
    (operator MM0ExpressionRefusedV1 1)

    (operator MM0AssertionEntryV1 5)
    (operator MM0AssertionLookupV1 3)
    (operator MM0AssertionFoundV1 2)
    (operator MM0AssertionEntriesAppendV1 3)
    (operator MM0AssertionStatementV1 5)
    (operator MM0AssertionStepV1 4)
    (operator MM0AssertionStepAfterLookupV1 8)
    (operator MM0AssertionStepAfterValidationV1 6)
    (operator MM0AssertionValidateV1 6)
    (operator MM0AssertionAfterExplicitItemsV1 7)
    (operator MM0AssertionAfterArrowV1 7)
    (operator MM0AssertionAfterPartitionV1 6)
    (operator MM0AssertionAfterBindersV1 7)
    (operator MM0AssertionAfterHypothesesV1 7)
    (operator MM0AssertionAfterConclusionV1 5)

    (operator MM0AssertionItemsFromAstV1 4)
    (operator MM0AssertionItemsPrependV1 3)
    (operator MM0AssertionArrowNormalizeV1 4)
    (operator MM0AssertionArrowPrependV1 3)
    (operator MM0AssertionArrowV1 2)
    (operator MM0AssertionTypedItemV1 1)
    (operator MM0AssertionHypothesisItemV1 2)
    (operator MM0AssertionPartitionV1 2)
    (operator MM0AssertionPartitionTypedV1 4)
    (operator MM0AssertionPartitionTypedPrependV1 3)
    (operator MM0AssertionPartitionHypothesesV1 4)
    (operator MM0AssertionPartitionHypothesisPrependV1 3)

    (operator MM0AssertionHypothesesV1 6)
    (operator MM0AssertionHypothesisAfterExpressionV1 8)
    (operator MM0HypothesisEntriesFromNamesV1 4)
    (operator MM0HypothesisEntriesPrependV1 3)
    (operator MM0HypothesisV1 2)
    (operator MM0AssertionSignatureV1 3)
    (operator MM0DeclaredAssertionV1 4)

    (operator MM0AssertionStepAcceptedV1 2)
    (operator MM0AssertionStepRefusedV1 3)
    (operator MM0StatementClassV1 2)
    (operator MM0SourceStepByClassV1 5)
    (operator MM0SourceStepAcceptedV1 2)
    (operator MM0SourceStepRefusedV1 3)

    (operator MM0RefusedAssertionRedeclarationV1 3)
    (operator MM0RefusedAssertionBinderOrderV1 2)
    (operator MM0RefusedAssertionConclusionTypeV1 2)

    (operator MM0DeclarationEntriesAppendV1 3)
    (operator MM0DeclarationFoundV1 2)
    (operator MM0ValidateArrowTypeV1 6)
    (operator MM0TermTailV1 2)
    (operator MM0SortLookupV1 3)
    (operator MM0SortFoundV1 2)
    (operator MM0SortModifiersV1 4)
    (operator MM0BinderV1 3)
    (operator MM0NamedBinderV1 1)
    (operator MM0TypeV1 2)
    (operator MM0TermSignatureV1 2)
    (operator MM0BinderLookupV1 3)
    (operator MM0BinderFoundV1 1)
    (operator MM0NameLookupV1 3)
    (operator MM0TermSignatureFoundV1 2)
    (operator MM0MathScalarsFromListV1 2)
    (operator MM0RuntimeExpressionElaborateV1 5)
    (operator MM0ExpressionVariableV1 2)
    (operator MM0ExpressionTermApplicationV1 3)
    (operator MM0ExpressionArgumentsConsV1 2)

    (operator MM0DefinitionStatementV1 5)
    (operator MM0DefinitionGroupsV1 2)
    (operator MM0DefinitionSplitGroupsV1 2)
    (operator MM0DefinitionSplitGroupV1 2)
    (operator MM0DefinitionSplitNamesV1 4)
    (operator MM0DefinitionOrdinaryGroupV1 4)
    (operator MM0DefinitionPrependPublicV1 3)
    (operator MM0DefinitionPrependDummyV1 3)
    (operator MM0DefinitionJoinGroupsV1 3)
    (operator MM0DefinitionRequestV1 5)
    (operator MM0DefinitionValidateV1 7)
    (operator MM0DefinitionAfterPublicV1 4)
    (operator MM0DefinitionAfterReturnV1 7)
    (operator MM0DefinitionAfterDummiesV1 4)
    (operator MM0DefinitionDummySortsV1 5)
    (operator MM0DefinitionAfterDummySortV1 7)
    (operator MM0DefinitionAfterDummySortsV1 5)
    (operator MM0DefinitionAfterBodyV1 4)
    (operator MM0DefinitionValidatedV1 3)
    (operator MM0DefinitionValueV1 8)
    (operator MM0DefinitionAfterExpressionV1 7)
    (operator MM0DefinitionAfterSupportV1 3)

    (operator MM0DefinitionFreeV1 4)
    (operator MM0DefinitionVariableFreeV1 3)
    (operator MM0DefinitionImageV1 2)
    (operator MM0DefinitionArgumentImagesV1 3)
    (operator MM0DefinitionImageLookupV1 3)
    (operator MM0DefinitionImageNamesV1 3)
    (operator MM0DefinitionArgumentsFreeV1 6)
    (operator MM0DefinitionSubtractNamesV1 3)
    (operator MM0DefinitionSubtractAfterLookupV1 5)
    (operator MM0DefinitionSubsetNamesV1 5)
    (operator MM0DefinitionSubsetAfterLookupV1 7)

    (operator MM0DefinitionStepV1 4)
    (operator MM0DefinitionStepAfterLookupV1 8)
    (operator MM0DefinitionStepAfterValidationV1 5)
    (operator MM0DefinitionSourceV1 3)
    (operator MM0DeclaredDefinitionV1 5)
    (operator MM0RefusedDefinitionRedeclarationV1 3)
    (operator MM0RefusedFreeDummySortV1 3)
    (operator MM0RefusedDefinitionDummiesWithoutBodyV1 2)
    (operator MM0RefusedDefinitionResultSortV1 4)
    (operator MM0RefusedDefinitionFreeVariableV1 3)
    (operator MM0CoercionViewV1 3)
    (operator MM0ExpressionCoerceV1 5)
    (operator MM0DefinitionAfterCoercionV1 8)
    (operator MM0RefusedExpressionSortV1 4))
  (equations)
  (rewrites
    ; Assertions share the declaration sequence with terms so source order is
    ; retained, but MM0 gives terms and assertions distinct name spaces.
    (rule mm0-declaration-lookup-skip-assertion-v1
      (head
        (MM0DeclarationLookupV1
          ?name
          (MM0DeclarationEntriesConsV1
            (MM0AssertionEntryV1
              ?kind ?assertionName ?signature ?position ?source)
            ?rest)
          ?result))
      (body
        (MM0DeclarationLookupV1 ?name ?rest ?result)))
    (rule mm0-term-signature-lookup-skip-assertion-v1
      (head
        (MM0TermSignatureLookupV1
          ?name
          (MM0DeclarationEntriesConsV1
            (MM0AssertionEntryV1
              ?kind ?assertionName ?signature ?position ?source)
            ?rest)
          ?result))
      (body
        (MM0TermSignatureLookupV1 ?name ?rest ?result)))

    (rule mm0-math-term-token-arity-skip-assertion-v1
      (head
        (MM0MathTermTokenArityLookupV1
          ?scalars
          (MM0DeclarationEntriesConsV1
            (MM0AssertionEntryV1
              ?kind ?assertionName ?signature ?position ?source)
            ?rest)
          ?name ?arity))
      (body
        (MM0MathTermTokenArityLookupV1
          ?scalars ?rest ?name ?arity)))

    (rule mm0-assertion-lookup-missing-v1
      (head
        (MM0AssertionLookupV1
          ?name MM0DeclarationEntriesNilV1 MM0AssertionMissingV1))
      (body))
    (rule mm0-assertion-lookup-found-v1
      (head
        (MM0AssertionLookupV1
          ?name
          (MM0DeclarationEntriesConsV1
            (MM0AssertionEntryV1
              ?kind ?name ?signature ?position ?source)
            ?rest)
          (MM0AssertionFoundV1 ?kind ?position)))
      (body))
    (rule mm0-assertion-lookup-other-assertion-v1
      (head
        (MM0AssertionLookupV1
          ?name
          (MM0DeclarationEntriesConsV1
            (MM0AssertionEntryV1
              ?kind ?other ?signature ?position ?source)
            ?rest)
          ?result))
      (body
        (different ?name ?other)
        (MM0AssertionLookupV1 ?name ?rest ?result)))
    (rule mm0-assertion-lookup-skip-term-v1
      (head
        (MM0AssertionLookupV1
          ?name
          (MM0DeclarationEntriesConsV1
            (MM0TermEntryV1
              ?termName ?signature ?position ?source)
            ?rest)
          ?result))
      (body
        (MM0AssertionLookupV1 ?name ?rest ?result)))

    (rule mm0-assertion-entries-append-nil-v1
      (head
        (MM0AssertionEntriesAppendV1
          MM0DeclarationEntriesNilV1 ?entry
          (MM0DeclarationEntriesConsV1
            ?entry MM0DeclarationEntriesNilV1)))
      (body))
    (rule mm0-assertion-entries-append-cons-v1
      (head
        (MM0AssertionEntriesAppendV1
          (MM0DeclarationEntriesConsV1 ?head ?rest) ?entry
          (MM0DeclarationEntriesConsV1 ?head ?after)))
      (body
        (MM0AssertionEntriesAppendV1 ?rest ?entry ?after)))

    ; The outer grammar retains assertion kind, label, binder groups, and the
    ; recursive arrow syntax without specializing them to either target.
    (rule mm0-axiom-statement-v1
      (head
        (MM0AssertionStatementV1
          (node mm0-assertion-statement
            (pair
              (node mm0-axiom-kind ?keyword)
              (pair ?identifier (pair ?binders ?arrow))))
          MM0AxiomDeclarationV1 ?name ?binders ?arrow))
      (body
        (MM0IdentifierScalarsV1 ?identifier ?name)))
    (rule mm0-theorem-statement-v1
      (head
        (MM0AssertionStatementV1
          (node mm0-assertion-statement
            (pair
              (node mm0-theorem-kind ?keyword)
              (pair ?identifier (pair ?binders ?arrow))))
          MM0TheoremDeclarationV1 ?name ?binders ?arrow))
      (body
        (MM0IdentifierScalarsV1 ?identifier ?name)))

    ; Convert the explicit binder syntax to a neutral ordered item list.
    ; Type items are later validated by the existing term-binder semantics;
    ; formula items become proof hypotheses.
    (rule mm0-assertion-items-nil-v1
      (head
        (MM0AssertionItemsFromAstV1
          ?position ?name nil (MM0CheckAcceptedV1 nil)))
      (body))
    (rule mm0-assertion-items-bound-v1
      (head
        (MM0AssertionItemsFromAstV1
          ?position ?name
          (cons
            (node mm0-formula-binder-bound (pair ?names ?type)) ?rest)
          ?result))
      (body
        (MM0AssertionItemsFromAstV1
          ?position ?name ?rest ?restResult)
        (MM0AssertionItemsPrependV1
          (MM0AssertionTypedItemV1
            (node mm0-type-binder-bound (pair ?names ?type)))
          ?restResult ?result)))
    (rule mm0-assertion-items-regular-type-v1
      (head
        (MM0AssertionItemsFromAstV1
          ?position ?name
          (cons
            (node mm0-formula-binder-regular
              (pair ?names (node mm0-type ?typePayload)))
            ?rest)
          ?result))
      (body
        (MM0AssertionItemsFromAstV1
          ?position ?name ?rest ?restResult)
        (MM0AssertionItemsPrependV1
          (MM0AssertionTypedItemV1
            (node mm0-type-binder-regular
              (pair ?names (node mm0-type ?typePayload))))
          ?restResult ?result)))
    (rule mm0-assertion-items-hypothesis-v1
      (head
        (MM0AssertionItemsFromAstV1
          ?position ?name
          (cons
            (node mm0-formula-binder-regular
              (pair ?names (node mm0-math-string ?scalars)))
            ?rest)
          ?result))
      (body
        (MM0AssertionItemsFromAstV1
          ?position ?name ?rest ?restResult)
        (MM0AssertionItemsPrependV1
          (MM0AssertionHypothesisItemV1 ?names ?scalars)
          ?restResult ?result)))
    (rule mm0-assertion-items-prepend-accepted-v1
      (head
        (MM0AssertionItemsPrependV1
          ?item (MM0CheckAcceptedV1 ?rest)
          (MM0CheckAcceptedV1 (cons ?item ?rest))))
      (body))
    (rule mm0-assertion-items-prepend-refused-v1
      (head
        (MM0AssertionItemsPrependV1
          ?item (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))

    ; Every non-final arrow unit is an anonymous binder or hypothesis.  The
    ; final unit must be a formula, exactly as in MM0's parseArrows/elaboration.
    (rule mm0-assertion-arrow-conclusion-v1
      (head
        (MM0AssertionArrowNormalizeV1
          ?position ?name
          (node mm0-formula-arrow-type
            (pair (node mm0-math-string ?scalars) none))
          (MM0CheckAcceptedV1 (MM0AssertionArrowV1 nil ?scalars))))
      (body))
    (rule mm0-assertion-arrow-conclusion-type-v1
      (head
        (MM0AssertionArrowNormalizeV1
          ?position ?name
          (node mm0-formula-arrow-type
            (pair (node mm0-type ?typePayload) none))
          (MM0CheckRefusedV1
            (MM0RefusedAssertionConclusionTypeV1 ?position ?name))))
      (body))
    (rule mm0-assertion-arrow-type-argument-v1
      (head
        (MM0AssertionArrowNormalizeV1
          ?position ?name
          (node mm0-formula-arrow-type
            (pair (node mm0-type ?typePayload) (some ?tail)))
          ?result))
      (body
        (MM0AssertionArrowNormalizeV1
          ?position ?name ?tail ?tailResult)
        (MM0AssertionArrowPrependV1
          (MM0AssertionTypedItemV1
            (node mm0-type-binder-regular
              (pair
                (cons
                  (node mm0-anonymous MM0ArrowAnonymousSourceV1) nil)
                (node mm0-type ?typePayload))))
          ?tailResult ?result)))
    (rule mm0-assertion-arrow-hypothesis-v1
      (head
        (MM0AssertionArrowNormalizeV1
          ?position ?name
          (node mm0-formula-arrow-type
            (pair (node mm0-math-string ?scalars) (some ?tail)))
          ?result))
      (body
        (MM0AssertionArrowNormalizeV1
          ?position ?name ?tail ?tailResult)
        (MM0AssertionArrowPrependV1
          (MM0AssertionHypothesisItemV1
            (cons MM0AnonymousHypothesisNameV1 nil) ?scalars)
          ?tailResult ?result)))
    (rule mm0-assertion-arrow-prepend-accepted-v1
      (head
        (MM0AssertionArrowPrependV1
          ?item
          (MM0CheckAcceptedV1
            (MM0AssertionArrowV1 ?items ?conclusion))
          (MM0CheckAcceptedV1
            (MM0AssertionArrowV1 (cons ?item ?items) ?conclusion))))
      (body))
    (rule mm0-assertion-arrow-prepend-refused-v1
      (head
        (MM0AssertionArrowPrependV1
          ?item (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))

    ; Typed binders must form a prefix.  Once a hypothesis appears, a later
    ; typed binder would not admit the ctx ++ hyps split required by MM0.
    (rule mm0-assertion-partition-typed-nil-v1
      (head
        (MM0AssertionPartitionTypedV1
          ?position ?name nil
          (MM0CheckAcceptedV1
            (MM0AssertionPartitionV1 nil nil))))
      (body))
    (rule mm0-assertion-partition-typed-cons-v1
      (head
        (MM0AssertionPartitionTypedV1
          ?position ?name
          (cons (MM0AssertionTypedItemV1 ?group) ?rest)
          ?result))
      (body
        (MM0AssertionPartitionTypedV1
          ?position ?name ?rest ?restResult)
        (MM0AssertionPartitionTypedPrependV1
          ?group ?restResult ?result)))
    (rule mm0-assertion-partition-first-hypothesis-v1
      (head
        (MM0AssertionPartitionTypedV1
          ?position ?name
          (cons (MM0AssertionHypothesisItemV1 ?names ?scalars) ?rest)
          ?result))
      (body
        (MM0AssertionPartitionHypothesesV1
          ?position ?name
          (cons (MM0AssertionHypothesisItemV1 ?names ?scalars) ?rest)
          ?hypothesisResult)
        (MM0AssertionPartitionTypedPrependV1
          MM0NoTypedBinderV1 ?hypothesisResult ?result)))
    (rule mm0-assertion-partition-typed-prepend-v1
      (head
        (MM0AssertionPartitionTypedPrependV1
          ?group
          (MM0CheckAcceptedV1
            (MM0AssertionPartitionV1 ?groups ?hypotheses))
          (MM0CheckAcceptedV1
            (MM0AssertionPartitionV1
              (cons ?group ?groups) ?hypotheses))))
      (body
        (different ?group MM0NoTypedBinderV1)))
    (rule mm0-assertion-partition-no-typed-prepend-v1
      (head
        (MM0AssertionPartitionTypedPrependV1
          MM0NoTypedBinderV1
          (MM0CheckAcceptedV1
            (MM0AssertionPartitionV1 ?groups ?hypotheses))
          (MM0CheckAcceptedV1
            (MM0AssertionPartitionV1 ?groups ?hypotheses))))
      (body))
    (rule mm0-assertion-partition-typed-prepend-refused-v1
      (head
        (MM0AssertionPartitionTypedPrependV1
          ?group (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))

    (rule mm0-assertion-partition-hypotheses-nil-v1
      (head
        (MM0AssertionPartitionHypothesesV1
          ?position ?name nil
          (MM0CheckAcceptedV1
            (MM0AssertionPartitionV1 nil nil))))
      (body))
    (rule mm0-assertion-partition-hypotheses-cons-v1
      (head
        (MM0AssertionPartitionHypothesesV1
          ?position ?name
          (cons (MM0AssertionHypothesisItemV1 ?names ?scalars) ?rest)
          ?result))
      (body
        (MM0AssertionPartitionHypothesesV1
          ?position ?name ?rest ?restResult)
        (MM0AssertionPartitionHypothesisPrependV1
          (MM0AssertionHypothesisItemV1 ?names ?scalars)
          ?restResult ?result)))
    (rule mm0-assertion-partition-hypotheses-typed-v1
      (head
        (MM0AssertionPartitionHypothesesV1
          ?position ?name
          (cons (MM0AssertionTypedItemV1 ?group) ?rest)
          (MM0CheckRefusedV1
            (MM0RefusedAssertionBinderOrderV1 ?position ?name))))
      (body))
    (rule mm0-assertion-partition-hypothesis-prepend-v1
      (head
        (MM0AssertionPartitionHypothesisPrependV1
          ?hypothesis
          (MM0CheckAcceptedV1
            (MM0AssertionPartitionV1 ?groups ?hypotheses))
          (MM0CheckAcceptedV1
            (MM0AssertionPartitionV1
              ?groups (cons ?hypothesis ?hypotheses)))))
      (body))
    (rule mm0-assertion-partition-hypothesis-prepend-refused-v1
      (head
        (MM0AssertionPartitionHypothesisPrependV1
          ?hypothesis (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))

    ; Elaborate hypotheses using the same live parser and ExprProv relation as
    ; conclusions.  Labels are retained for the later .mmb proof stage.
    (rule mm0-assertion-hypotheses-nil-v1
      (head
        (MM0AssertionHypothesesV1
          ?position ?state ?context nil ?name
          (MM0CheckAcceptedV1 nil)))
      (body))
    (rule mm0-assertion-hypotheses-cons-v1
      (head
        (MM0AssertionHypothesesV1
          ?position ?state ?context
          (cons
            (MM0AssertionHypothesisItemV1 ?names ?scalars) ?rest)
          ?name ?result))
      (body
        (MM0MathScalarsFromListV1 ?scalars ?mathScalars)
        (MM0RuntimeProvableExpressionElaborateV1
          ?position ?state ?context ?mathScalars ?expressionResult)
        (MM0AssertionHypothesisAfterExpressionV1
          ?position ?state ?context ?names ?rest ?name
          ?expressionResult ?result)))
    (rule mm0-assertion-hypothesis-expression-refused-v1
      (head
        (MM0AssertionHypothesisAfterExpressionV1
          ?position ?state ?context ?names ?rest ?name
          (MM0ExpressionRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-assertion-hypothesis-expression-accepted-v1
      (head
        (MM0AssertionHypothesisAfterExpressionV1
          ?position ?state ?context ?names ?rest ?name
          (MM0ExpressionAcceptedV1 ?expression ?sort) ?result))
      (body
        (MM0AssertionHypothesesV1
          ?position ?state ?context ?rest ?name ?restResult)
        (MM0HypothesisEntriesFromNamesV1
          ?names ?expression ?restResult ?result)))
    (rule mm0-hypothesis-entries-nil-v1
      (head
        (MM0HypothesisEntriesFromNamesV1
          nil ?expression ?restResult ?restResult))
      (body))
    (rule mm0-hypothesis-entries-cons-v1
      (head
        (MM0HypothesisEntriesFromNamesV1
          (cons ?hypothesisName ?names) ?expression ?restResult ?result))
      (body
        (MM0HypothesisEntriesFromNamesV1
          ?names ?expression ?restResult ?afterNames)
        (MM0HypothesisEntriesPrependV1
          (MM0HypothesisV1 ?hypothesisName ?expression)
          ?afterNames ?result)))
    (rule mm0-hypothesis-entries-prepend-accepted-v1
      (head
        (MM0HypothesisEntriesPrependV1
          ?hypothesis (MM0CheckAcceptedV1 ?rest)
          (MM0CheckAcceptedV1 (cons ?hypothesis ?rest))))
      (body))
    (rule mm0-hypothesis-entries-prepend-refused-v1
      (head
        (MM0HypothesisEntriesPrependV1
          ?hypothesis (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))

    ; Validation pipeline: normalize syntax, partition the ordered context,
    ; reuse term-binder checks, then elaborate hypotheses and conclusion.
    (rule mm0-assertion-validate-v1
      (head
        (MM0AssertionValidateV1
          ?position ?name ?state ?binders ?arrow ?result))
      (body
        (MM0AssertionItemsFromAstV1
          ?position ?name ?binders ?itemsResult)
        (MM0AssertionAfterExplicitItemsV1
          ?position ?name ?state ?arrow ?binders ?itemsResult ?result)))
    (rule mm0-assertion-explicit-items-refused-v1
      (head
        (MM0AssertionAfterExplicitItemsV1
          ?position ?name ?state ?arrow ?binders
          (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-assertion-explicit-items-accepted-v1
      (head
        (MM0AssertionAfterExplicitItemsV1
          ?position ?name ?state ?arrow ?binders
          (MM0CheckAcceptedV1 ?explicitItems) ?result))
      (body
        (MM0AssertionArrowNormalizeV1
          ?position ?name ?arrow ?arrowResult)
        (MM0AssertionAfterArrowV1
          ?position ?name ?state ?explicitItems ?binders
          ?arrowResult ?result)))
    (rule mm0-assertion-arrow-refused-v1
      (head
        (MM0AssertionAfterArrowV1
          ?position ?name ?state ?explicitItems ?binders
          (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-assertion-arrow-accepted-v1
      (head
        (MM0AssertionAfterArrowV1
          ?position ?name ?state ?explicitItems ?binders
          (MM0CheckAcceptedV1
            (MM0AssertionArrowV1 ?arrowItems ?conclusion))
          ?result))
      (body
        (MM0ListAppendV1 ?explicitItems ?arrowItems ?items)
        (MM0AssertionPartitionTypedV1
          ?position ?name ?items ?partitionResult)
        (MM0AssertionAfterPartitionV1
          ?position ?name ?state ?conclusion ?partitionResult ?result)))
    (rule mm0-assertion-partition-refused-v1
      (head
        (MM0AssertionAfterPartitionV1
          ?position ?name ?state ?conclusion
          (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-assertion-partition-accepted-v1
      (head
        (MM0AssertionAfterPartitionV1
          ?position ?name
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          ?conclusion
          (MM0CheckAcceptedV1
            (MM0AssertionPartitionV1 ?typedGroups ?hypotheses))
          ?result))
      (body
        (MM0ValidateExplicitBindersV1
          ?position ?name ?sorts ?typedGroups nil nil ?binderResult)
        (MM0AssertionAfterBindersV1
          ?position ?name
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          ?conclusion ?hypotheses ?binderResult ?result)))
    (rule mm0-assertion-binders-refused-v1
      (head
        (MM0AssertionAfterBindersV1
          ?position ?name ?state ?conclusion ?hypotheses
          (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-assertion-binders-accepted-v1
      (head
        (MM0AssertionAfterBindersV1
          ?position ?name ?state ?conclusion ?hypotheses
          (MM0CheckAcceptedV1
            (MM0BinderSequenceV1 ?context ?boundNames ?allNames))
          ?result))
      (body
        (MM0AssertionHypothesesV1
          ?position ?state ?context ?hypotheses ?name ?hypothesisResult)
        (MM0AssertionAfterHypothesesV1
          ?position ?name ?state ?context ?conclusion
          ?hypothesisResult ?result)))
    (rule mm0-assertion-hypotheses-refused-v1
      (head
        (MM0AssertionAfterHypothesesV1
          ?position ?name ?state ?context ?conclusion
          (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-assertion-hypotheses-accepted-v1
      (head
        (MM0AssertionAfterHypothesesV1
          ?position ?name ?state ?context ?conclusion
          (MM0CheckAcceptedV1 ?hypotheses) ?result))
      (body
        (MM0MathScalarsFromListV1 ?conclusion ?mathScalars)
        (MM0RuntimeProvableExpressionElaborateV1
          ?position ?state ?context ?mathScalars ?conclusionResult)
        (MM0AssertionAfterConclusionV1
          ?position ?context ?hypotheses ?conclusionResult ?result)))
    (rule mm0-assertion-conclusion-refused-v1
      (head
        (MM0AssertionAfterConclusionV1
          ?position ?context ?hypotheses
          (MM0ExpressionRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-assertion-conclusion-accepted-v1
      (head
        (MM0AssertionAfterConclusionV1
          ?position ?context ?hypotheses
          (MM0ExpressionAcceptedV1 ?conclusion ?sort)
          (MM0CheckAcceptedV1
            (MM0AssertionSignatureV1
              ?context ?hypotheses ?conclusion))))
      (body))

    ; Ordered transition and source-fold integration.
    (rule mm0-assertion-step-v1
      (head
        (MM0AssertionStepV1
          ?position ?statement
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          ?result))
      (body
        (MM0AssertionStatementV1
          ?statement ?kind ?name ?binders ?arrow)
        (MM0AssertionLookupV1 ?name ?declarations ?lookup)
        (MM0AssertionStepAfterLookupV1
          ?position ?kind ?name ?binders ?arrow
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          ?lookup ?result)))
    (rule mm0-assertion-step-redeclared-v1
      (head
        (MM0AssertionStepAfterLookupV1
          ?position ?kind ?name ?binders ?arrow ?before
          (MM0AssertionFoundV1 ?oldKind ?firstPosition)
          (MM0AssertionStepRefusedV1
            (MM0RefusedAssertionRedeclarationV1
              ?position ?name ?firstPosition)
            ?before
            (MM0RefusedAssertionRedeclarationV1
              ?position ?name ?firstPosition))))
      (body))
    (rule mm0-assertion-step-fresh-v1
      (head
        (MM0AssertionStepAfterLookupV1
          ?position ?kind ?name ?binders ?arrow ?before
          MM0AssertionMissingV1 ?result))
      (body
        (MM0AssertionValidateV1
          ?position ?name ?before ?binders ?arrow ?validation)
        (MM0AssertionStepAfterValidationV1
          ?position ?kind ?name ?before ?validation ?result)))
    (rule mm0-assertion-step-validation-refused-v1
      (head
        (MM0AssertionStepAfterValidationV1
          ?position ?kind ?name ?before
          (MM0CheckRefusedV1 ?reason)
          (MM0AssertionStepRefusedV1 ?reason ?before ?reason)))
      (body))
    (rule mm0-assertion-step-validation-accepted-v1
      (head
        (MM0AssertionStepAfterValidationV1
          ?position ?kind ?name
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          (MM0CheckAcceptedV1 ?signature)
          (MM0AssertionStepAcceptedV1
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?afterDeclarations) ?notation)
            (MM0DeclaredAssertionV1
              ?position ?kind ?name ?signature))))
      (body
        (MM0AssertionEntriesAppendV1
          ?declarations
          (MM0AssertionEntryV1
            ?kind ?name ?signature ?position MM0RuntimeTextualSourceV1)
          ?afterDeclarations)))

    ; splitDummies preserves public and dummy order independently. A dot name
    ; is a local bound variable in either bracket style; an anonymous name is
    ; a regular argument, including inside braces, as in the MM0 parser.
    (rule mm0-definition-statement-v1
      (head
        (MM0DefinitionStatementV1
          (node mm0-definition-statement
            (pair ?identifier (pair ?groups (pair ?type ?value))))
          ?name ?groups ?type ?value))
      (body
        (MM0IdentifierScalarsV1 ?identifier ?name)))
    (rule mm0-definition-split-groups-nil-v1
      (head
        (MM0DefinitionSplitGroupsV1 nil (MM0DefinitionGroupsV1 nil nil)))
      (body))
    (rule mm0-definition-split-groups-cons-v1
      (head
        (MM0DefinitionSplitGroupsV1 (cons ?group ?rest) ?result))
      (body
        (MM0DefinitionSplitGroupV1 ?group ?first)
        (MM0DefinitionSplitGroupsV1 ?rest ?tail)
        (MM0DefinitionJoinGroupsV1 ?first ?tail ?result)))
    (rule mm0-definition-split-bound-group-v1
      (head
        (MM0DefinitionSplitGroupV1
          (node mm0-dummy-binder-bound (pair ?names ?type)) ?result))
      (body
        (MM0DefinitionSplitNamesV1
          MM0BoundBinderKindV1 ?names ?type ?result)))
    (rule mm0-definition-split-regular-group-v1
      (head
        (MM0DefinitionSplitGroupV1
          (node mm0-dummy-binder-regular (pair ?names ?type)) ?result))
      (body
        (MM0DefinitionSplitNamesV1
          MM0RegularBinderKindV1 ?names ?type ?result)))
    (rule mm0-definition-split-names-nil-v1
      (head
        (MM0DefinitionSplitNamesV1
          ?kind nil ?type (MM0DefinitionGroupsV1 nil nil)))
      (body))
    (rule mm0-definition-split-names-dummy-v1
      (head
        (MM0DefinitionSplitNamesV1
          ?kind
          (cons (node mm0-dummy-identifier-dot ?identifier) ?rest)
          ?type ?result))
      (body
        (MM0DefinitionSplitNamesV1 ?kind ?rest ?type ?tail)
        (MM0DefinitionPrependDummyV1
          (node mm0-type-binder-bound
            (pair (cons ?identifier nil) ?type))
          ?tail ?result)))
    (rule mm0-definition-split-names-public-v1
      (head
        (MM0DefinitionSplitNamesV1
          ?kind (cons (node mm0-identifier ?payload) ?rest) ?type ?result))
      (body
        (MM0DefinitionOrdinaryGroupV1
          ?kind (node mm0-identifier ?payload) ?type ?group)
        (MM0DefinitionSplitNamesV1 ?kind ?rest ?type ?tail)
        (MM0DefinitionPrependPublicV1 ?group ?tail ?result)))
    (rule mm0-definition-split-names-anonymous-v1
      (head
        (MM0DefinitionSplitNamesV1
          ?kind (cons (node mm0-anonymous ?payload) ?rest) ?type ?result))
      (body
        (MM0DefinitionSplitNamesV1 ?kind ?rest ?type ?tail)
        (MM0DefinitionPrependPublicV1
          (node mm0-type-binder-regular
            (pair (cons (node mm0-anonymous ?payload) nil) ?type))
          ?tail ?result)))
    (rule mm0-definition-ordinary-bound-group-v1
      (head
        (MM0DefinitionOrdinaryGroupV1
          MM0BoundBinderKindV1 ?identifier ?type
          (node mm0-type-binder-bound
            (pair (cons ?identifier nil) ?type))))
      (body))
    (rule mm0-definition-ordinary-regular-group-v1
      (head
        (MM0DefinitionOrdinaryGroupV1
          MM0RegularBinderKindV1 ?identifier ?type
          (node mm0-type-binder-regular
            (pair (cons ?identifier nil) ?type))))
      (body))
    (rule mm0-definition-prepend-public-v1
      (head
        (MM0DefinitionPrependPublicV1
          ?group (MM0DefinitionGroupsV1 ?public ?dummies)
          (MM0DefinitionGroupsV1 (cons ?group ?public) ?dummies)))
      (body))
    (rule mm0-definition-prepend-dummy-v1
      (head
        (MM0DefinitionPrependDummyV1
          ?group (MM0DefinitionGroupsV1 ?public ?dummies)
          (MM0DefinitionGroupsV1 ?public (cons ?group ?dummies))))
      (body))
    (rule mm0-definition-join-groups-v1
      (head
        (MM0DefinitionJoinGroupsV1
          (MM0DefinitionGroupsV1 ?leftPublic ?leftDummies)
          (MM0DefinitionGroupsV1 ?rightPublic ?rightDummies)
          (MM0DefinitionGroupsV1 ?public ?dummies)))
      (body
        (MM0ListAppendV1 ?leftPublic ?rightPublic ?public)
        (MM0ListAppendV1 ?leftDummies ?rightDummies ?dummies)))

    ; Validate the exposed context and return dependencies before introducing
    ; local dummies. This prevents public types from depending on a dummy.
    ; As for a term declaration, every non-final unit of the declared arrow
    ; type is an anonymous regular argument after the explicit ones.
    (rule mm0-definition-validate-v1
      (head
        (MM0DefinitionValidateV1
          ?position ?name
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          ?groups ?type ?value ?result))
      (body
        (MM0DefinitionSplitGroupsV1
          ?groups (MM0DefinitionGroupsV1 ?public ?dummies))
        (MM0ValidateExplicitBindersV1
          ?position ?name ?sorts ?public nil nil ?publicResult)
        (MM0DefinitionAfterPublicV1
          (MM0DefinitionRequestV1
            ?position ?name
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
            ?type ?value)
          ?dummies ?publicResult ?result)))
    (rule mm0-definition-public-refused-v1
      (head
        (MM0DefinitionAfterPublicV1
          ?request ?dummies (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-definition-public-accepted-v1
      (head
        (MM0DefinitionAfterPublicV1
          (MM0DefinitionRequestV1
            ?position ?name
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
            ?type ?value)
          ?dummies
          (MM0CheckAcceptedV1
            (MM0BinderSequenceV1 ?public ?boundNames ?allNames))
          ?result))
      (body
        (MM0ValidateArrowTypeV1
          ?position ?name ?sorts ?boundNames ?type ?returnResult)
        (MM0DefinitionAfterReturnV1
          (MM0DefinitionRequestV1
            ?position ?name
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
            ?type ?value)
          ?dummies ?public ?boundNames ?allNames ?returnResult ?result)))
    (rule mm0-definition-return-refused-v1
      (head
        (MM0DefinitionAfterReturnV1
          ?request ?dummies ?public ?boundNames ?allNames
          (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-definition-return-accepted-v1
      (head
        (MM0DefinitionAfterReturnV1
          (MM0DefinitionRequestV1
            ?position ?name
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
            ?type ?value)
          ?dummies ?public ?boundNames ?allNames
          (MM0CheckAcceptedV1 (MM0TermTailV1 ?arrowBinders ?returnType))
          ?result))
      (body
        (MM0ValidateExplicitBindersV1
          ?position ?name ?sorts ?dummies ?boundNames ?allNames ?dummyResult)
        (MM0ListAppendV1 ?public ?arrowBinders ?signatureBinders)
        (MM0DefinitionAfterDummiesV1
          (MM0DefinitionRequestV1
            ?position ?name
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
            ?type ?value)
          (MM0TermSignatureV1 ?signatureBinders ?returnType)
          ?dummyResult ?result)))
    (rule mm0-definition-dummies-refused-v1
      (head
        (MM0DefinitionAfterDummiesV1
          ?request ?signature (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-definition-dummies-accepted-v1
      (head
        (MM0DefinitionAfterDummiesV1
          (MM0DefinitionRequestV1
            ?position ?name
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
            ?type ?value)
          ?signature
          (MM0CheckAcceptedV1
            (MM0BinderSequenceV1 ?dummies ?boundNames ?allNames)) ?result))
      (body
        (MM0DefinitionDummySortsV1
          ?position ?name ?sorts ?dummies ?dummySortResult)
        (MM0DefinitionAfterDummySortsV1
          (MM0DefinitionRequestV1
            ?position ?name
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
            ?type ?value)
          ?signature ?dummies ?dummySortResult ?result)))
    (rule mm0-definition-dummy-sorts-nil-v1
      (head
        (MM0DefinitionDummySortsV1
          ?position ?name ?sorts nil
          (MM0CheckAcceptedV1 MM0DefinitionDummySortsAcceptedV1)))
      (body))
    (rule mm0-definition-dummy-sorts-cons-v1
      (head
        (MM0DefinitionDummySortsV1
          ?position ?name ?sorts
          (cons
            (MM0BinderV1 MM0BoundBinderKindV1 ?binder
              (MM0TypeV1 ?sort nil)) ?rest)
          ?result))
      (body
        (MM0SortLookupV1 ?sort ?sorts ?lookup)
        (MM0DefinitionAfterDummySortV1
          ?position ?name ?sorts ?sort ?rest ?lookup ?result)))
    (rule mm0-definition-dummy-sort-free-v1
      (head
        (MM0DefinitionAfterDummySortV1
          ?position ?name ?sorts ?sort ?rest
          (MM0SortFoundV1
            (MM0SortModifiersV1
              ?pure ?strict ?provable MM0ModifierPresentV1) ?first)
          (MM0CheckRefusedV1
            (MM0RefusedFreeDummySortV1 ?position ?name ?sort))))
      (body))
    (rule mm0-definition-dummy-sort-accepted-v1
      (head
        (MM0DefinitionAfterDummySortV1
          ?position ?name ?sorts ?sort ?rest
          (MM0SortFoundV1
            (MM0SortModifiersV1
              ?pure MM0ModifierAbsentV1 ?provable MM0ModifierAbsentV1) ?first)
          ?result))
      (body
        (MM0DefinitionDummySortsV1 ?position ?name ?sorts ?rest ?result)))
    (rule mm0-definition-dummy-sorts-refused-v1
      (head
        (MM0DefinitionAfterDummySortsV1
          ?request ?signature ?dummies (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-definition-dummy-sorts-accepted-v1
      (head
        (MM0DefinitionAfterDummySortsV1
          (MM0DefinitionRequestV1 ?position ?name ?state ?type ?value)
          (MM0TermSignatureV1 ?public ?returnType) ?dummies
          (MM0CheckAcceptedV1 MM0DefinitionDummySortsAcceptedV1) ?result))
      (body
        (MM0ListAppendV1 ?public ?dummies ?context)
        (MM0DefinitionValueV1
          ?position ?name ?state ?context ?returnType ?dummies ?value ?bodyResult)
        (MM0DefinitionAfterBodyV1
          (MM0TermSignatureV1 ?public ?returnType) ?dummies ?bodyResult ?result)))
    (rule mm0-definition-body-refused-v1
      (head
        (MM0DefinitionAfterBodyV1
          ?signature ?dummies (MM0CheckRefusedV1 ?reason)
          (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-definition-body-accepted-v1
      (head
        (MM0DefinitionAfterBodyV1
          ?signature ?dummies (MM0CheckAcceptedV1 ?body)
          (MM0CheckAcceptedV1
            (MM0DefinitionValidatedV1 ?signature ?dummies ?body))))
      (body))

    ; A missing definiens remains None, rather than an invented body. Dummies
    ; have no meaning without a body (elabDefO0 in the MM0 self-specification).
    (rule mm0-definition-value-none-v1
      (head
        (MM0DefinitionValueV1
          ?position ?name ?state ?context ?returnType nil none
          (MM0CheckAcceptedV1 none)))
      (body))
    (rule mm0-definition-value-none-dummies-v1
      (head
        (MM0DefinitionValueV1
          ?position ?name ?state ?context ?returnType
          (cons ?dummy ?rest) none
          (MM0CheckRefusedV1
            (MM0RefusedDefinitionDummiesWithoutBodyV1 ?position ?name))))
      (body))
    (rule mm0-definition-value-some-v1
      (head
        (MM0DefinitionValueV1
          ?position ?name ?state ?context ?returnType ?dummies
          (some (node mm0-math-string ?scalars)) ?result))
      (body
        (MM0MathScalarsFromListV1 ?scalars ?mathScalars)
        (MM0RuntimeExpressionElaborateV1
          ?position ?state ?context ?mathScalars ?expressionResult)
        (MM0DefinitionAfterExpressionV1
          ?position ?name ?state ?context ?returnType ?expressionResult ?result)))
    (rule mm0-definition-value-expression-refused-v1
      (head
        (MM0DefinitionAfterExpressionV1
          ?position ?name ?state ?context ?returnType
          (MM0ExpressionRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-definition-value-sort-refused-v1
      (head
        (MM0DefinitionAfterExpressionV1
          ?position ?name (MM0SourceStateV1 ?textual ?notation) ?context (MM0TypeV1 ?expected ?deps)
          (MM0ExpressionAcceptedV1 ?expression ?actual)
          ?result))
      (body
        (different ?expected ?actual)
        (MM0CoercionViewV1 ?notation ?base ?edges)
        (MM0ExpressionCoerceV1 ?position ?expected ?edges
          (MM0ExpressionAcceptedV1 ?expression ?actual) ?coerced)
        (MM0DefinitionAfterCoercionV1 ?position ?name
          (MM0SourceStateV1 ?textual ?notation) ?context
          (MM0TypeV1 ?expected ?deps) ?actual ?coerced ?result)))
    (rule mm0-definition-value-coercion-missing-v1
      (head (MM0DefinitionAfterCoercionV1 ?position ?name ?state ?context
        (MM0TypeV1 ?expected ?deps) ?actual
        (MM0ExpressionRefusedV1 (MM0RefusedExpressionSortV1 ?position ?expression ?expected ?actual))
        (MM0CheckRefusedV1 (MM0RefusedDefinitionResultSortV1 ?position ?name ?expected ?actual)))) (body))
    (rule mm0-definition-value-coercion-accepted-v1
      (head (MM0DefinitionAfterCoercionV1 ?position ?name ?state ?context
        (MM0TypeV1 ?expected ?deps) ?actual
        (MM0ExpressionAcceptedV1 ?expression ?expected) ?result))
      (body (MM0DefinitionAfterExpressionV1 ?position ?name ?state ?context
        (MM0TypeV1 ?expected ?deps) (MM0ExpressionAcceptedV1 ?expression ?expected) ?result)))
    (rule mm0-definition-value-sort-accepted-v1
      (head
        (MM0DefinitionAfterExpressionV1
          ?position ?name
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          ?context (MM0TypeV1 ?sort ?deps)
          (MM0ExpressionAcceptedV1 ?expression ?sort) ?result))
      (body
        (MM0DefinitionFreeV1 ?declarations ?context ?expression ?free)
        (MM0DefinitionSubsetNamesV1 ?position ?name ?free ?deps ?supportResult)
        (MM0DefinitionAfterSupportV1 ?expression ?supportResult ?result)))
    (rule mm0-definition-value-support-refused-v1
      (head
        (MM0DefinitionAfterSupportV1
          ?expression (MM0CheckRefusedV1 ?reason) (MM0CheckRefusedV1 ?reason)))
      (body))
    (rule mm0-definition-value-support-accepted-v1
      (head
        (MM0DefinitionAfterSupportV1
          ?expression (MM0CheckAcceptedV1 MM0DefinitionSupportAcceptedV1)
          (MM0CheckAcceptedV1 (some ?expression))))
      (body))

    ; Free variables follow the signature's binding information. A bound
    ; actual argument supplies an image for a formal bound name. Each regular
    ; argument removes images of its formal dependencies; return dependencies
    ; add their images back. Raw names are sets represented by membership lists.
    (rule mm0-definition-free-variable-v1
      (head
        (MM0DefinitionFreeV1
          ?declarations ?context (MM0ExpressionVariableV1 ?name ?sort) ?free))
      (body
        (MM0BinderLookupV1 ?name ?context ?lookup)
        (MM0DefinitionVariableFreeV1 ?name ?lookup ?free)))
    (rule mm0-definition-variable-free-bound-v1
      (head
        (MM0DefinitionVariableFreeV1
          ?name
          (MM0BinderFoundV1
            (MM0BinderV1 MM0BoundBinderKindV1 ?binder ?type))
          (cons ?name nil)))
      (body))
    (rule mm0-definition-variable-free-regular-v1
      (head
        (MM0DefinitionVariableFreeV1
          ?name
          (MM0BinderFoundV1
            (MM0BinderV1 MM0RegularBinderKindV1 ?binder
              (MM0TypeV1 ?sort ?deps))) ?deps))
      (body))
    (rule mm0-definition-free-application-v1
      (head
        (MM0DefinitionFreeV1
          ?declarations ?context
          (MM0ExpressionTermApplicationV1 ?name ?arguments ?sort) ?free))
      (body
        (MM0TermSignatureLookupV1
          ?name ?declarations
          (MM0TermSignatureFoundV1
            (MM0TermSignatureV1 ?binders (MM0TypeV1 ?sort ?returnDeps)) ?position))
        (MM0DefinitionArgumentImagesV1 ?binders ?arguments ?images)
        (MM0DefinitionArgumentsFreeV1
          ?declarations ?context ?images ?binders ?arguments ?argumentFree)
        (MM0DefinitionImageNamesV1 ?returnDeps ?images ?returnFree)
        (MM0ListAppendV1 ?argumentFree ?returnFree ?free)))
    (rule mm0-definition-argument-images-nil-v1
      (head
        (MM0DefinitionArgumentImagesV1 nil MM0ExpressionArgumentsNilV1 nil))
      (body))
    (rule mm0-definition-argument-images-bound-v1
      (head
        (MM0DefinitionArgumentImagesV1
          (cons
            (MM0BinderV1 MM0BoundBinderKindV1 (MM0NamedBinderV1 ?formal) ?type)
            ?binders)
          (MM0ExpressionArgumentsConsV1
            (MM0ExpressionVariableV1 ?actual ?sort) ?arguments)
          (cons (MM0DefinitionImageV1 ?formal ?actual) ?images)))
      (body
        (MM0DefinitionArgumentImagesV1 ?binders ?arguments ?images)))
    (rule mm0-definition-argument-images-regular-v1
      (head
        (MM0DefinitionArgumentImagesV1
          (cons (MM0BinderV1 MM0RegularBinderKindV1 ?binder ?type) ?binders)
          (MM0ExpressionArgumentsConsV1 ?argument ?arguments) ?images))
      (body
        (MM0DefinitionArgumentImagesV1 ?binders ?arguments ?images)))
    (rule mm0-definition-image-lookup-found-v1
      (head
        (MM0DefinitionImageLookupV1
          ?formal (cons (MM0DefinitionImageV1 ?formal ?actual) ?rest) ?actual))
      (body))
    (rule mm0-definition-image-lookup-tail-v1
      (head
        (MM0DefinitionImageLookupV1
          ?formal (cons (MM0DefinitionImageV1 ?other ?actual) ?rest) ?result))
      (body
        (different ?formal ?other)
        (MM0DefinitionImageLookupV1 ?formal ?rest ?result)))
    (rule mm0-definition-image-names-nil-v1
      (head (MM0DefinitionImageNamesV1 nil ?images nil))
      (body))
    (rule mm0-definition-image-names-cons-v1
      (head
        (MM0DefinitionImageNamesV1
          (cons ?formal ?rest) ?images (cons ?actual ?tail)))
      (body
        (MM0DefinitionImageLookupV1 ?formal ?images ?actual)
        (MM0DefinitionImageNamesV1 ?rest ?images ?tail)))
    (rule mm0-definition-arguments-free-nil-v1
      (head
        (MM0DefinitionArgumentsFreeV1
          ?declarations ?context ?images nil MM0ExpressionArgumentsNilV1 nil))
      (body))
    (rule mm0-definition-arguments-free-bound-v1
      (head
        (MM0DefinitionArgumentsFreeV1
          ?declarations ?context ?images
          (cons (MM0BinderV1 MM0BoundBinderKindV1 ?binder ?type) ?binders)
          (MM0ExpressionArgumentsConsV1 ?argument ?arguments) ?free))
      (body
        (MM0DefinitionArgumentsFreeV1
          ?declarations ?context ?images ?binders ?arguments ?free)))
    (rule mm0-definition-arguments-free-regular-v1
      (head
        (MM0DefinitionArgumentsFreeV1
          ?declarations ?context ?images
          (cons
            (MM0BinderV1 MM0RegularBinderKindV1 ?binder (MM0TypeV1 ?sort ?deps))
            ?binders)
          (MM0ExpressionArgumentsConsV1 ?argument ?arguments) ?free))
      (body
        (MM0DefinitionFreeV1 ?declarations ?context ?argument ?argumentFree)
        (MM0DefinitionImageNamesV1 ?deps ?images ?boundImages)
        (MM0DefinitionSubtractNamesV1 ?argumentFree ?boundImages ?unbound)
        (MM0DefinitionArgumentsFreeV1
          ?declarations ?context ?images ?binders ?arguments ?restFree)
        (MM0ListAppendV1 ?unbound ?restFree ?free)))
    (rule mm0-definition-subtract-names-nil-v1
      (head (MM0DefinitionSubtractNamesV1 nil ?mask nil))
      (body))
    (rule mm0-definition-subtract-names-cons-v1
      (head
        (MM0DefinitionSubtractNamesV1 (cons ?name ?rest) ?mask ?result))
      (body
        (MM0NameLookupV1 ?name ?mask ?lookup)
        (MM0DefinitionSubtractAfterLookupV1 ?name ?rest ?mask ?lookup ?result)))
    (rule mm0-definition-subtract-names-found-v1
      (head
        (MM0DefinitionSubtractAfterLookupV1
          ?name ?rest ?mask MM0NameFoundV1 ?result))
      (body
        (MM0DefinitionSubtractNamesV1 ?rest ?mask ?result)))
    (rule mm0-definition-subtract-names-missing-v1
      (head
        (MM0DefinitionSubtractAfterLookupV1
          ?name ?rest ?mask MM0NameMissingV1 (cons ?name ?tail)))
      (body
        (MM0DefinitionSubtractNamesV1 ?rest ?mask ?tail)))
    (rule mm0-definition-subset-names-nil-v1
      (head
        (MM0DefinitionSubsetNamesV1
          ?position ?name nil ?deps
          (MM0CheckAcceptedV1 MM0DefinitionSupportAcceptedV1)))
      (body))
    (rule mm0-definition-subset-names-cons-v1
      (head
        (MM0DefinitionSubsetNamesV1
          ?position ?name (cons ?variable ?rest) ?deps ?result))
      (body
        (MM0NameLookupV1 ?variable ?deps ?lookup)
        (MM0DefinitionSubsetAfterLookupV1
          ?position ?name ?variable ?rest ?deps ?lookup ?result)))
    (rule mm0-definition-subset-names-found-v1
      (head
        (MM0DefinitionSubsetAfterLookupV1
          ?position ?name ?variable ?rest ?deps MM0NameFoundV1 ?result))
      (body
        (MM0DefinitionSubsetNamesV1 ?position ?name ?rest ?deps ?result)))
    (rule mm0-definition-subset-names-missing-v1
      (head
        (MM0DefinitionSubsetAfterLookupV1
          ?position ?name ?variable ?rest ?deps MM0NameMissingV1
          (MM0CheckRefusedV1
            (MM0RefusedDefinitionFreeVariableV1 ?position ?name ?variable))))
      (body))

    ; A body elaborates against the preceding environment. Definitions then
    ; extend exactly the same term lookup used by term declarations and syntax.
    (rule mm0-definition-step-v1
      (head
        (MM0DefinitionStepV1
          ?position ?statement
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation) ?result))
      (body
        (MM0DefinitionStatementV1 ?statement ?name ?groups ?type ?value)
        (MM0DeclarationLookupV1 ?name ?declarations ?lookup)
        (MM0DefinitionStepAfterLookupV1
          ?position ?name ?groups ?type ?value
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          ?lookup ?result)))
    (rule mm0-definition-step-redeclared-v1
      (head
        (MM0DefinitionStepAfterLookupV1
          ?position ?name ?groups ?type ?value ?before
          (MM0DeclarationFoundV1 ?kind ?first)
          (MM0SourceStepRefusedV1
            (MM0RefusedDefinitionRedeclarationV1 ?position ?name ?first) ?before
            (MM0RefusedDefinitionRedeclarationV1 ?position ?name ?first))))
      (body))
    (rule mm0-definition-step-fresh-v1
      (head
        (MM0DefinitionStepAfterLookupV1
          ?position ?name ?groups ?type ?value ?before MM0DeclarationMissingV1
          ?result))
      (body
        (MM0DefinitionValidateV1
          ?position ?name ?before ?groups ?type ?value ?validation)
        (MM0DefinitionStepAfterValidationV1
          ?position ?name ?before ?validation ?result)))
    (rule mm0-definition-step-validation-refused-v1
      (head
        (MM0DefinitionStepAfterValidationV1
          ?position ?name ?before (MM0CheckRefusedV1 ?reason)
          (MM0SourceStepRefusedV1 ?reason ?before ?reason)))
      (body))
    (rule mm0-definition-step-validation-accepted-v1
      (head
        (MM0DefinitionStepAfterValidationV1
          ?position ?name
          (MM0SourceStateV1
            (MM0TextualEnvironmentV1 ?sorts ?declarations) ?notation)
          (MM0CheckAcceptedV1
            (MM0DefinitionValidatedV1 ?signature ?dummies ?body))
          (MM0SourceStepAcceptedV1
            (MM0SourceStateV1
              (MM0TextualEnvironmentV1 ?sorts ?afterDeclarations) ?notation)
            (MM0DeclaredDefinitionV1 ?position ?name ?signature ?dummies ?body))))
      (body
        (MM0DeclarationEntriesAppendV1
          ?declarations
          (MM0TermEntryV1 ?name ?signature ?position
            (MM0DefinitionSourceV1 ?dummies ?body MM0RuntimeTextualSourceV1))
          ?afterDeclarations)))
    (rule mm0-source-statement-class-definition-v1
      (head
        (MM0StatementClassV1
          (node mm0-definition-statement ?payload) MM0DefinitionStatementClassV1))
      (body))
    (rule mm0-source-step-definition-v1
      (head
        (MM0SourceStepByClassV1
          ?position ?statement ?before MM0DefinitionStatementClassV1 ?result))
      (body
        (MM0DefinitionStepV1 ?position ?statement ?before ?result)))

    (rule mm0-source-statement-class-assertion-v1
      (head
        (MM0StatementClassV1
          (node mm0-assertion-statement ?payload)
          MM0AssertionStatementClassV1))
      (body))
    (rule mm0-source-step-assertion-accepted-v1
      (head
        (MM0SourceStepByClassV1
          ?position ?statement ?before MM0AssertionStatementClassV1
          (MM0SourceStepAcceptedV1 ?after ?historyEntry)))
      (body
        (MM0AssertionStepV1
          ?position ?statement ?before
          (MM0AssertionStepAcceptedV1 ?after ?historyEntry))))
    (rule mm0-source-step-assertion-refused-v1
      (head
        (MM0SourceStepByClassV1
          ?position ?statement ?before MM0AssertionStatementClassV1
          (MM0SourceStepRefusedV1 ?reason ?before ?historyEntry)))
      (body
        (MM0AssertionStepV1
          ?position ?statement ?before
          (MM0AssertionStepRefusedV1
            ?reason ?before ?historyEntry))))
  ))

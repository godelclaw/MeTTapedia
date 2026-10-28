; One retained constructor-row inspection. Full rows and continuations remain
; in the pending scan; only the typing view is projected for readiness.

(: gslt:collection-presentation:view-scan-row (-> Atom %Undefined%))
(= (gslt:collection-presentation:view-scan-row $row)
  (case $row
    (((GrammarRuleV2 $label $category $parameters $syntax $evaluation $algebra)
       (ConstructorScanRow (GrammarTypingV1 $label $category $parameters) $parameters))
     ((GrammarRuleWrappedV2 $label $category $parameters $syntax $evaluation $algebra)
       (ConstructorScanRow (GrammarTypingWrappedV1 $label $category $parameters) $parameters)))))

(: gslt:collection-presentation:view-scan-focus (-> Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-scan-focus $category $focus)
  (case $focus
    (((ViewOriginal $bound $expected $source $context) (ViewFocusTyping $bound $expected))
     ((ViewGrouped $bound $components) (ViewFocusTyping $bound (TBase $category))))))

(: gslt:collection-presentation:view-scan-constructors
  (-> Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-scan-constructors
     $sorts $declarations $free $schema-free $category $task)
  (case $task
    (((ViewConstructors $schema-bound $path $focus $label $schemas $sources $outer $ordinal $remaining $next)
       (case $remaining
         ((LNil (ViewExpansion LNil LNil))
          ((LCons $row $later)
            (let* (($typing (gslt:collection-presentation:view-scan-row $row))
                   ($scope (gslt:collection-presentation:view-scan-focus $category $focus))
                   ($following (+ $ordinal 1)))
              (case (ConstructorScanInputs $typing $scope)
                (((ConstructorScanInputs
                    (ConstructorScanRow $typed-row $parameters) (ViewFocusTyping $bound $expected))
                   (let $scan (ViewConstructors $schema-bound $path $focus $label $schemas $sources
                                $outer $following $later $next)
                     (if (gslt:collection-presentation:view-constructor-ready
                           $sorts $declarations $free $schema-free $schema-bound $bound $expected
                           $label $schemas $sources $typed-row)
                       (let $parent (ViewFrame $path $schema-bound $focus (Some $ordinal) None)
                         (ViewExpansion
                           (LCons (ViewRequest ViewChildrenKind
                             (ViewArguments $schema-bound $path $bound $label $outer $sources 0
                               $schemas $sources $parameters)
                             (ViewApplication $parent $label $next))
                             (LCons $scan LNil))
                           LNil))
                       (ViewExpansion (LCons $scan LNil) LNil))))))))))))))

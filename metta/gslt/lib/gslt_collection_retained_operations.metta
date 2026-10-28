; Retained return continuations, child requests, state commit and readout.
; Return continuations and child queries share the complete retained state codec.

(: gslt:collection-presentation:view-values (-> Atom %Undefined%))
(= (gslt:collection-presentation:view-values $occurrences)
  (case $occurrences
    ((LNil LNil)
     ((LCons (AlgebraSourceOccurrence $original $address $context $value) $later)
       (let $rest (gslt:collection-presentation:view-values $later)
         (LCons $value $rest))))))

(: gslt:collection-presentation:view-return (-> Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-return $value $continuation)
  (case (ViewReturnPair $value $continuation)
    (((ViewReturnPair (ViewSpelling $target $frames) ViewDone)
       (ViewExpansion LNil (LCons (ViewSpelling $target $frames) LNil)))
     ((ViewReturnPair (ViewChildren $targets $frames) (ViewApplication $parent $label $next))
       (ViewExpansion
         (LCons (ViewReturned ViewSpellingKind
           (ViewSpelling (PApp $label $targets) (LCons $parent $frames)) $next) LNil)
         LNil))
     ((ViewReturnPair (ViewChildren $targets $frames) (ViewCollection $parent $residual $next))
       (let* (($values (gslt:collection-presentation:view-values $residual))
              ($items (gslt:automata:append $targets $values)))
         (ViewExpansion
           (LCons (ViewReturned ViewSpellingKind
             (ViewSpelling
               (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $items RNone)
               (LCons $parent $frames)) $next) LNil)
           LNil)))
     ((ViewReturnPair (ViewSpelling $target $frames) (ViewLambda $parent $binder $next))
       (ViewExpansion
         (LCons (ViewReturned ViewSpellingKind
           (ViewSpelling (PLam $binder $target) (LCons $parent $frames)) $next) LNil)
         LNil))
     ((ViewReturnPair (ViewSpelling $target $frames) (ViewMultiLambda $parent $arity $binders $next))
       (ViewExpansion
         (LCons (ViewReturned ViewSpellingKind
           (ViewSpelling (PMultiLam $arity $binders $target) (LCons $parent $frames)) $next) LNil)
         LNil))
     ((ViewReturnPair (ViewSpelling $target $frames) (ViewTail $query $next))
       (ViewExpansion
         (LCons (ViewRequest ViewChildrenKind $query
           (ViewPrepend (ViewSpelling $target $frames) $next)) LNil)
         LNil))
     ((ViewReturnPair (ViewChildren $targets $frames) (ViewPrepend (ViewSpelling $head $headFrames) $next))
       (let $joined (gslt:automata:append $headFrames $frames)
         (ViewExpansion
           (LCons (ViewReturned ViewChildrenKind
             (ViewChildren (LCons $head $targets) $joined) $next) LNil)
           LNil))))))

(: gslt:collection-presentation:view-context-comp (-> Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-context-comp $outer $inner)
  (case $outer
    ((ContextHole $inner)
     ((ContextApp $label $before $context $after)
       (let $composed (gslt:collection-presentation:view-context-comp $context $inner)
         (ContextApp $label $before $composed $after)))
     ((ContextLam $binder $context)
       (let $composed (gslt:collection-presentation:view-context-comp $context $inner)
         (ContextLam $binder $composed)))
     ((ContextMultiLam $arity $binders $context)
       (let $composed (gslt:collection-presentation:view-context-comp $context $inner)
         (ContextMultiLam $arity $binders $composed)))
     ((ContextSubstBody $context $replacement)
       (let $composed (gslt:collection-presentation:view-context-comp $context $inner)
         (ContextSubstBody $composed $replacement)))
     ((ContextSubstReplacement $body $context)
       (let $composed (gslt:collection-presentation:view-context-comp $context $inner)
         (ContextSubstReplacement $body $composed)))
     ((ContextCollection $kind $before $context $after $rest)
       (let $composed (gslt:collection-presentation:view-context-comp $context $inner)
         (ContextCollection $kind $before $composed $after $rest))))))

(: gslt:collection-presentation:view-children (-> Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-children $query $next)
  (case $query
    (((ViewArguments $schema-bound $path $bound $label $outer $originals $index
        LNil LNil LNil)
       (ViewExpansion (LCons (ViewReturned ViewChildrenKind (ViewChildren LNil LNil) $next) LNil) LNil))
     ((ViewArguments $schema-bound $path $bound $label (Some $context) $originals $index
        (LCons $schema $schemas) (LCons $source $sources) (LCons $parameter $parameters))
       (case (gslt:premise:parameter-type $parameter)
         ((None (ViewExpansion LNil LNil))
          ((Some $expected)
            (let* (($before (gslt:complete:take $index $originals))
                   ($following (+ $index 1))
                   ($after (gslt:complete:drop $following $originals))
                   ($child-context (gslt:collection-presentation:view-context-comp
                     $context (ContextApp $label $before ContextHole $after)))
                   ($child-path (gslt:automata:append $path (LCons $index LNil))))
              (ViewExpansion
                (LCons (ViewRequest ViewSpellingKind
                  (ViewAt $schema-bound $child-path $schema
                    (ViewOriginal $bound $expected $source $child-context))
                  (ViewTail (ViewArguments $schema-bound $path $bound $label (Some $context)
                    $originals $following $schemas $sources $parameters) $next)) LNil)
                LNil))))))
     ((ViewGroups $schema-bound $path $bound $index LNil LNil)
       (ViewExpansion (LCons (ViewReturned ViewChildrenKind (ViewChildren LNil LNil) $next) LNil) LNil))
     ((ViewGroups $schema-bound $path $bound $index (LCons $schema $schemas) (LCons $group $groups))
       (let* (($child-path (gslt:automata:append $path (LCons $index LNil)))
              ($following (+ $index 1)))
         (ViewExpansion
           (LCons (ViewRequest ViewSpellingKind
             (ViewAt $schema-bound $child-path $schema (ViewGrouped $bound $group))
             (ViewTail (ViewGroups $schema-bound $path $bound $following $schemas $groups) $next)) LNil)
           LNil)))
     ($bad (ViewExpansion LNil LNil)))))

(: gslt:collection-presentation:view-commit (-> Atom Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-commit $pending $answers $expansion)
  (case $expansion
    (((ViewExpansion $children $published)
      (let* (($agenda (gslt:automata:append $children $pending))
             ($account (gslt:automata:append $answers $published)))
        (ViewState $agenda $account))))))


(: gslt:collection-presentation:view-complete (-> Atom %Undefined%))
(= (gslt:collection-presentation:view-complete $state)
  (case $state
    (((ViewState $agenda $answers)
      (case $agenda ((LNil True) ((LCons $task $pending) False)))))))

(: gslt:collection-presentation:view-answers (-> Atom %Undefined%))
(= (gslt:collection-presentation:view-answers $state)
  (case $state (((ViewState $agenda $answers) $answers))))

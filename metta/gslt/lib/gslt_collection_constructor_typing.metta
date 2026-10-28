; Constructor readiness for the retained recursive presentation producer.
; Target and schema scopes are separate. The declaration scan retains the
; authored row and ordinal; these functions do not grant admission.

(: gslt:collection-presentation:view-constructor-arguments
  (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-constructor-arguments
     $sorts $declarations $free $schema-free $schema-bound $bound $schemas $sources $parameters)
  (if (gslt:premise:type-arguments $declarations $free $bound $sources $parameters)
    (gslt:premise:schema-arguments
      $sorts $declarations $schema-free $schema-bound $schemas $parameters)
    False))

(: gslt:collection-presentation:view-constructor-parameters
  (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-constructor-parameters
     $sorts $declarations $free $schema-free $schema-bound $bound $schemas $sources $parameters $mode)
  (case (ConstructorParameters $mode $parameters)
    (((ConstructorParameters ConstructorBare
        (LCons (TermSimple $parameter (TCollection $kind $element)) LNil)) False)
     ((ConstructorParameters ConstructorBare $ordinary)
       (gslt:collection-presentation:view-constructor-arguments
         $sorts $declarations $free $schema-free $schema-bound $bound $schemas $sources $ordinary))
     ((ConstructorParameters ConstructorWrapped $ordinary)
       (gslt:collection-presentation:view-constructor-arguments
         $sorts $declarations $free $schema-free $schema-bound $bound $schemas $sources $ordinary))
     ($other False))))

(: gslt:collection-presentation:view-constructor-ready
  (-> Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom Atom %Undefined%))
(= (gslt:collection-presentation:view-constructor-ready
     $sorts $declarations $free $schema-free $schema-bound $bound $expected $label $schemas $sources $row)
  (case $row
    (((GrammarTypingV1 $actual $category $parameters)
       (if (== $actual $label)
         (let $result (TBase $category)
           (if (== $expected $result)
             (gslt:collection-presentation:view-constructor-parameters
               $sorts $declarations $free $schema-free $schema-bound $bound $schemas $sources $parameters ConstructorBare)
             False))
         False))
     ((GrammarTypingWrappedV1 $actual $category $parameters)
       (if (== $actual $label)
         (let $result (TBase $category)
           (if (== $expected $result)
             (gslt:collection-presentation:view-constructor-parameters
               $sorts $declarations $free $schema-free $schema-bound $bound $schemas $sources $parameters ConstructorWrapped)
             False))
         False))
     ($other False))))

; Fold a captured constructor node after folding its ordered recursive children.
(: gslt:inductive:fold (-> Atom Atom %Undefined%))
(= (gslt:inductive:fold $method $tree)
  (case $tree
    (((InductiveNode $shape $children)
      (let $folded (gslt:inductive:fold-children $method $children)
        (let $application (cons-atom $method ($shape $folded))
          (eval $application)))))))

(: gslt:inductive:fold-children (-> Atom Atom %Undefined%))
(= (gslt:inductive:fold-children $method $children)
  (case $children
    ((LNil LNil)
     ((LCons $child $rest)
      (let $folded (gslt:inductive:fold $method $child)
        (let $tail (gslt:inductive:fold-children $method $rest)
          (LCons $folded $tail)))))))

; A concrete constructor method retaining every transformed descendant.
(: gslt:inductive:rebuild (-> Atom Atom %Undefined%))
(= (gslt:inductive:rebuild $shape $children)
  (FoldedNode $shape $children))

; Captured constructor data may itself have executable-looking syntax.
(: gslt:inductive:return-shape (-> Atom Atom %Undefined%))
(= (gslt:inductive:return-shape $shape $children) $shape)

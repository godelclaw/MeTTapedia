; Constructor methods for the admitted SearchTree answer-collecting recursor.
(: gslt:inductive:append-results (-> Atom Atom %Undefined%))
(= (gslt:inductive:append-results $first $second)
  (case $first
    ((LNil $second)
     ((LCons $head $tail)
      (let $rest (gslt:inductive:append-results $tail $second)
        (LCons $head $rest))))))

(: gslt:inductive:flatten-results (-> Atom %Undefined%))
(= (gslt:inductive:flatten-results $lists)
  (case $lists
    ((LNil LNil)
     ((LCons $first $rest)
      (let $tail (gslt:inductive:flatten-results $rest)
        (gslt:inductive:append-results $first $tail))))))

(: gslt:inductive:search-answers (-> Atom Atom %Undefined%))
(= (gslt:inductive:search-answers $shape $children)
  (case $shape
    (((Solved $answer) (LCons $answer LNil))
     ((Branch $length) (gslt:inductive:flatten-results $children)))))

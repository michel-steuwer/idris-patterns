module skel.rules

import Data.VectType
import skel

%default total

-- rewrite rules

{-
iterateDecomp : {a: Type} -> {i: Size} -> {j: Size} ->
                (n: Size) -> (m: Size) ->
                (f: ({k : Size} -> Array a (i * k) -> Array a k) ) ->
                (xs: Array a ((power i (n + m)) * j)) ->
    iterate {a=a} {i=i} {j=j} (m + n) f xs
      = iterate {a=a} {i=i} {j=j} m f
        (iterate {a=a} {i=i} {j=(power i m) * j} n f xs)

iterateDecomp n m f = ?decomp
-}


reorderCommutativity : {a: Type} -> {b: Type} -> {i: Size} ->
                       (f: a -> b) -> (xs: Array a i) ->
    skel.map f . skel.reorder $ xs = skel.reorder . skel.map f $ xs

reorderCommutativity _ _ = Refl



splitJoin : {a: Type} -> {b: Type} -> {i: Size} ->
            (n: Size) -> (f: a -> b) -> (xs : Array a (n * i)) ->
    skel.map f xs = skel.join $ skel.map (skel.map f) $ skel.split n xs

splitJoin {a} {b} {i=i} Z _ Nil = ?sj_nil1
splitJoin {a} {b} {i=Z} n _ (rewrite (multZeroRightZero n) in Nil) = ?sj_nil2

splitJoin {a} {b} {i=S i0} n f xs =
  let xs' : Array a (n + n * i0) = rewrite sym (lemma1 n i0) in xs
      (a1, a2) : (Array a n, Array a (n * i0)) = splitAt n xs'
      --inductiveHypothesis1 = splitJoin {a} {b} {i=1}  n f (rewrite (multOneRightNeutral n) in a1)
      --inductiveHypothesis2 = splitJoin {a} {b} {i=i0} n f a2
    in ?sj_all


cancellationOne : {a: Type} -> {i: Size} ->
                  (n: Size) -> (xs: Array a (n * i)) ->
    skel.join . skel.split n $ xs = xs

cancellationOne {a} {i=Z}   Z Nil = Refl
cancellationOne {a} {i=S k} Z Nil =
  let xs : Array a (Z * k) = Nil
      inductiveHypothesis = cancellationOne {i=k} Z xs
      in ?jss_nil1

cancellationOne {a} {i=Z}   (S k) xs  =
  let ys: Array a Z = rewrite sym (multZeroRightZero (S k)) in xs
      in ?jss_nil2
cancellationOne {a} {i} (S k) xs  = ?jss


{-
cancellationTwo : {a: Type} -> {i: Size} ->
                  (j: Size) -> (xs: Array (Array a i) j) ->
    skel.split {i=j} i (skel.join {i=i} {j=j} xs) = xs

cancellationTwo = ?cancellationTwo_all
-}


fusionOne : {a: Type} -> {b: Type} -> {c: Type} -> {i: Size} ->
            (f: b -> c) -> (g: a -> b) -> (xs: Array a i) ->
    skel.map f (skel.map g xs) = skel.map (f . g) xs

fusionOne f g Nil       = Refl
fusionOne f g (x :: xs) =
  let inductiveHypothesis = fusionOne f g xs in
      ?fusionOneStepCase


fusionTwo : (f: (b,c) -> b) -> (g: a -> c) -> (z: b) -> (xs: Array a i) ->
    skel.reduceSeq f z (skel.mapSeq g xs)
      = skel.reduceSeq (\(acc, x) => f (acc, g x)) z xs

fusionTwo f g z Nil       = Refl
fusionTwo f g z (x :: xs) =
  let inductiveHypothesis = fusionTwo f g (f (z, g x)) xs in
      ?fusionTwoStepCase


mapRule1 : (f: a -> b) -> (xs: Array a i) ->
    skel.map f xs = skel.mapWorkgroup f xs

mapRule1 _ _ = Refl


mapRule2 : (f: a -> b) -> (xs: Array a i) ->
    skel.map f xs = skel.mapLocal f xs

mapRule2 _ _ = Refl


mapRule3 : (f: a -> b) -> (xs: Array a i) ->
    skel.map f xs = skel.mapGlobal f xs

mapRule3 _ _ = Refl


mapRule4 : (f: a -> b) -> (xs: Array a i) ->
    skel.map f xs = skel.mapSeq f xs

mapRule4 _ _ = Refl


reduceRule : (f: (a,a) -> a) -> (z: a) -> (xs: Array a i) ->
    skel.reduce f z xs = skel.reduceSeq f z xs

reduceRule f z Nil        = Refl
reduceRule f z (x :: xs)  =
  let inductiveHypothesis = reduceRule f (f (z, x)) xs in
      ?reduceRuleStepCase


reorderIdRule : (xs: Array a i) ->
    skel.reorder xs = xs

reorderIdRule _ = Refl


reorderStrideRule : (xs: Array a i) -> (n: Size) ->
    skel.reorder xs = skel.reorderStride n xs

reorderStrideRule _ _ = Refl


localMemRule : (f: a -> b) -> (xs: Array a i) ->
    skel.mapLocal f xs = skel.toLocal (skel.mapLocal f) xs

localMemRule _ _ = Refl


globalMemRule : (f: a -> b) -> (xs: Array a i) ->
    skel.mapLocal f xs = skel.toGlobal (skel.mapLocal f) xs

globalMemRule _ _ = Refl

vectorizationRule : {a: Type} -> {b: Type} -> {i: Size} ->
                    (n: Size) -> (f: a -> b) -> (xs : Array a (n * i)) ->
    skel.map f xs
      = skel.joinVec (skel.map (skel.mapVec f) (skel.splitVec n xs))

vectorizationRule n f xs = ?vectorizationRule_all




-- rules toomas

rule1 : {a: Type} -> {b: Type} -> {c: Type} -> {i: Size} ->
        (n: Size) -> (f: (a,b) -> c) ->
        (xs: Array a (n * i)) -> (ys: Array b (n * i)) ->
    skel.map f (skel.zip xs ys)
      = skel.join (skel.map (skel.map f) (skel.split n (skel.zip xs ys)))
rule1 n f xs ys = ?rule1_proof

{-
rule2 : {a: Type} -> {b: Type} -> {c: Type} -> {i: Size} ->
        (n: Size) -> (f: (a,b) -> c) ->
        (xs: Array a (n * i)) -> (ys: Array b (n * i)) ->
    skel.map f (skel.zip xs ys)
      = skel.join (skel.map (skel.map f) (skel.zip (skel.split n) (skel.split n)))
rule2 n f xs ys = ?rule2_proof
-}


{-
lemma3 : {a: Type} -> (k: Size) ->
          (Data.VectType.Vect.Nil {a=a})
            = replace (sym (replace (multZeroRightZero k) Refl))
                (Data.VectType.Vect.Nil {a=a})
lemma3 k = ?lemma3_proof
-}

---------- Proofs ----------

skel.rules.reduceRuleStepCase = proof
  intros
  rewrite sym inductiveHypothesis
  trivial


skel.rules.fusionOneStepCase = proof
  intros
  rewrite sym inductiveHypothesis
  trivial

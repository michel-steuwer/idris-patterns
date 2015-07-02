module skel

import Data.VectType

%default total

Size : Type
Size = Nat

Array : Type -> Size -> Type
Array a i = Vect i a

Vector : Type -> Size -> Type
Vector a i = Vect i a

-- lemmas

lemma1 : (n: Size) -> (i: Size) -> mult n (S i) = plus n (mult n i)
lemma1 n i = ?lemma1_proof

lemma2 : (a: Type) -> (n: Size) -> Array a Z = Array a (n * Z)
lemma2 _ n = ?lemma2_proof

lemma3 : {a: Type} -> (k: Size) ->
          (Data.VectType.Vect.Nil {a=a})
            = replace (sym (replace (multZeroRightZero k) Refl))
                (Data.VectType.Vect.Nil {a=a})
lemma3 k = ?lemma3_proof

-- algorithmic primitives

map : {a: Type} -> {b: Type} -> {i: Size} ->
      (a -> b) -> Array a i -> Array b i
map f Nil       = Nil
map f (x :: xs) = (f x) :: (map f xs)

zip : {a: Type} -> {b: Type} -> {i: Size} ->
      Array a i -> Array b i -> Array (a, b) i
zip Nil Nil = Nil
zip (x :: xs) (y :: ys) = (x, y) :: (skel.zip xs ys)

reduce : {a: Type} -> {i: Size} ->
      ((a,a) -> a) -> a -> Array a i -> Array a 1
reduce f z Nil        = (z :: Nil)
reduce f z (x :: xs)  = reduce f (f (z,x)) xs

split : {a: Type} -> {i: Size} ->
      (n: Size) -> Array a (n * i) -> Array (Array a n) i
split {a} {i=Z}   Z _ = Nil
split {a} {i=S k} Z _ = replicate (S k) Nil

split {a} {i=Z}   (S k) _  = Nil
split {a} {i=S k} n xs = a1 :: a2
  where
    take' : (n: Size) -> Array a (n + n * k) -> Array a n
    take' n = take n

    a1 : Array a n
    a1 = take' n (rewrite sym (lemma1 n k) in xs)

    drop' : (n: Size) -> Array a (n + n * k) -> Array a (n * k)
    drop' n = drop n

    a2 : Array (Array a n) k
    a2 = (skel.split n (drop' n (rewrite sym (lemma1 n k) in xs)))


join : {a: Type} -> {i: Size} -> {j: Size} ->
      Array (Array a i) j -> Array a (j * i)
join Nil = Nil
join {a} {i=Z} {j}   _ = rewrite (multZeroRightZero j) in Nil
join {a} {i}   {j=Z} _ = Nil
join (x :: xs) = x ++ (skel.join xs)

iterate : {a: Type} -> {i: Size} -> {j: Size} ->
      (n: Size) -> ( {m: Size} -> Array a (i * m) -> Array a m )
                -> Array a ((power i n) * j) -> Array a j
iterate {a} {i} {j} Z     f xs = (rewrite sym (plusZeroRightNeutral j) in xs)
iterate {a} {i} {j} (S n) f xs = iterate n f (f xs')
        where xs' = (rewrite (multAssociative i (power i n) j) in xs)

reorder : {a: Type} -> {i: Size} ->
      Array a i -> Array a i
reorder = id


-- OpenCL primitives
mapWorkgroup : {a: Type} -> {b: Type} -> {i: Size} ->
      (a -> b) -> Array a i -> Array b i
mapWorkgroup = skel.map

mapLocal : {a: Type} -> {b: Type} -> {i: Size} ->
      (a -> b) -> Array a i -> Array b i
mapLocal = skel.map

mapGlobal : {a: Type} -> {b: Type} -> {i: Size} ->
      (a -> b) -> Array a i -> Array b i
mapGlobal = skel.map

mapSeq : {a: Type} -> {b: Type} -> {i: Size} ->
      (a -> b) -> Array a i -> Array b i
mapSeq = skel.map

toLocal : {a: Type} -> {b: Type} -> {i: Size} ->
      (a -> b) -> (a -> b)
toLocal = id

toGlobal : {a: Type} -> {b: Type} -> {i: Size} ->
      (a -> b) -> (a -> b)
toGlobal = id

reduceSeq : {a: Type} -> {b: Type} -> {i: Size} ->
      ((a,b) -> a) -> a -> Array b i -> Array a 1
reduceSeq f z Nil        = (z :: Nil)
reduceSeq f z (x :: xs)  = reduceSeq f (f (z,x)) xs

reducePart : {a: Type} -> {i: Size} ->
      ((a,a) -> a) -> a -> (n: Size) -> Array a (n * i) -> Array a n
reducePart {a} {i} f z (S Z) = skel.reduce f z
reducePart {a} {i} f z k     =
   (rewrite sym (multOneRightNeutral k) in joinK)
 . skel.map (skel.reduce f z)
 . (rewrite sym (multCommutative i k) in splitI)
  where
    joinK  : Array (Array a 1) k -> Array a (k * 1)
    joinK  = skel.join {i=1} {j=k}

    splitI : Array a (i * k) -> Array (Array a i) k
    splitI = skel.split {i=k} i

reorderStride : {a: Type} -> {i: Size} ->
      (n: Size) -> Array a i -> Array a i
reorderStride _ = id

mapVec : {a: Type} -> {b: Type} ->
         {n: Size} -> (a -> b) -> Vector a n -> Vector b n
mapVec = skel.map

splitVec : {a: Type} -> {i: Size} ->
      (n: Size) -> Array a (n * i) -> Array (Vector a n) i
splitVec = split

joinVec : {a: Type} -> {i: Size} -> {j: Size} ->
      Array (Vector a i) j -> Vector a (j * i)
joinVec Nil = Nil
joinVec (x :: xs) = x ++ (joinVec xs)



-- rewrite rules
{-
iterateDecomp : {a: Type} -> {i: Size} -> {j: Size} ->
                (n: Size) -> (m: Size) ->
                (f: {k : Size} -> Array a (i * k) -> Array a k) ->
               iterate (m + n) f {a=a} {i=i} {j=j}
                =   iterate m f {a=a} {i=i} {j=j}
                  . iterate n f {a=a} {i=i} {j=(power i m) * j}
iterateDecomp n m = ?decomp
-}

reorderCommutativity : {a: Type} -> {b: Type} -> {i: Size} ->
                          (f: a -> b) -> (xs: Array a i) ->
    skel.map f . skel.reorder $ xs = skel.reorder . skel.map f $ xs
reorderCommutativity {a} {b} {i} f xs = ?reorderComm

splitJoin : {a: Type} -> {b: Type} -> {i: Size} ->
            (n: Size) -> (f: a -> b) -> (xs : Array a (n * i)) ->
            skel.map f xs = skel.join $ skel.map (skel.map f) $ skel.split n xs
splitJoin {a} {b} {i=Z}   Z _ Nil = Refl
splitJoin {a} {b} {i=S k} Z _ Nil = ?sj_nil1
splitJoin {a} {b} {i=Z}   (S k)  f (rewrite (multZeroRightZero k) in Nil) = ?sj_nil2
splitJoin {a} {b} {i=S i0} (S n0) f xs = ?sj_all


cancellationOne : {a: Type} -> {i: Size} ->
                  (n: Size) -> (xs: Array a (n * i)) ->
                  skel.join . skel.split n $ xs = xs
cancellationOne {a} {i=Z}   Z Nil = Refl
cancellationOne {a} {i=S k} Z Nil = ?jss_nil --sym (lemma2 a k)
cancellationOne {a} {i} (S k) xs  = ?jss

{-
cancellationTwo : {a: Type} -> {i: Size} ->
                  (j: Size) -> (xs: Array (Array a i) j) ->
                      skel.split {i=j} i . skel.join {i=i} {j=j} $ xs = xs
cancellationTwo = ?cancellationTwo_all
-}

fusionOne : {a: Type} -> {b: Type} -> {c: Type} -> {i: Size} ->
            (f: b -> c) -> (g: a -> b) -> (xs: Array a i) ->
            skel.map f (skel.map g xs) = skel.map (f . g) xs
fusionOne f g Nil       = Refl
fusionOne f g (x :: xs) =
  let inductiveHypothesis = fusionOne f g xs in
      ?fusionOneStepCase

fusionTwo : (f: (b,c) -> b) -> (z: b) -> (g: a -> c) -> (xs: Array a i) ->
            skel.reduceSeq f z (skel.mapSeq g xs)
              = skel.reduceSeq (\(acc, x) => f (acc, g x)) z xs
fusionTwo f z g Nil       = Refl
fusionTwo f z g (x :: xs) =
  let inductiveHypothesis = fusionTwo f z g xs in
      ?fusionTwoStepCase

mapRule1 : (f: a -> b) -> (xs: Array a i) ->
           skel.map f xs = skel.mapWorkgroup f xs
mapRule1 f xs = ?mapRules_all

mapRule2 : (f: a -> b) -> (xs: Array a i) ->
           skel.map f xs = skel.mapLocal f xs
mapRule2 f xs = ?mapRules_all

mapRule3 : (f: a -> b) -> (xs: Array a i) ->
           skel.map f xs = skel.mapGlobal f xs
mapRule3 f xs = ?mapRules_all

mapRule4 : (f: a -> b) -> (xs: Array a i) ->
           skel.map f xs = skel.mapSeq f xs
mapRule4 f xs = ?mapRules_all

reduceRule : (f: (a,a) -> a) -> (z: a) -> (xs: Array a i) ->
             skel.reduce f z xs = skel.reduceSeq f z xs
reduceRule f z xs = ?reduceRule_all

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

-- some tests

add : (Nat, Nat) -> Nat
add (x,y) = plus x y

times2 : Nat -> Nat
times2 x = x*2

xs : Array Nat 4
xs = [1, 2, 3, 4]

ys : Array (Nat, Nat) 4
ys = skel.zip xs (skel.map times2 xs)

zs : Array Nat 1
zs = reduce add 0 xs

---------- Proofs ----------

skel.mapRules_all = proof
  intros
  induction xs
  trivial
  intros
  rewrite ihv__0
  trivial


skel.fusionOneStepCase = proof
  intros
  rewrite sym inductiveHypothesis 
  trivial


skel.lemma2_proof = proof
  intros
  rewrite multZeroRightZero n
  trivial

skel.lemma1_proof = proof
  intros
  induction i
  rewrite sym (multZeroRightZero n)
  rewrite sym (multOneRightNeutral n)
  rewrite sym (plusZeroRightNeutral n)
  trivial
  intros
  rewrite (multRightSuccPlus n (S n__0))
  trivial


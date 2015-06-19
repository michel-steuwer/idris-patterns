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
lemma1 n i = ?l2

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
split {a} {i=Z}   n (rewrite (multZeroRightZero n) in Nil) = Nil
split {a} {i=S k} n xs  = a1 :: a2
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
      (n: Size) -> (a -> b) -> Vector a n -> Vector b n
mapVec _ = skel.map

splitVec : {a: Type} -> {i: Size} ->
      (n: Size) -> Array a (n * i) -> Array (Vector a n) i
splitVec = split

joinVec : {a: Type} -> {i: Size} -> {j: Size} ->
      Array (Vector a i) j -> Vector a (j * i)
joinVec Nil = Nil
joinVec (x :: xs) = x ++ (joinVec xs)



-- rewrite rules
{-
iterateDecomp : {a : Type} -> {i : Size} -> {j : Size} ->
                (n : Size) -> (m : Size)
                           -> (f : {k : Size} -> Array a (i * k) -> Array a k) ->
               iterate (m + n) f {a=a} {i=i} {j=j}
                =   iterate m f {a=a} {i=i} {j=j}
                  . iterate n f {a=a} {i=i} {j=(power i m) * j}
iterateDecomp n m = ?decomp
-}

splitJoin : {a : Type} -> {b : Type} -> {i : Size} ->
            (n : Size) -> (f : a -> b) -> (xs : Array a (n * i)) ->
            skel.map f xs = skel.join $ skel.map (skel.map f) $ skel.split n xs
splitJoin {a} {b} {i=Z} Z f Nil = ?sj_nil
splitJoin {a} {b} {i}   n f xs  = ?sj_cons


--joinSplitSimple1 : skel.join . skel.split n = id
joinSplitSimple1 : {a: Type} -> {b: Type} -> {i: Size} ->
                   (n: Size) -> (xs: Array a (n *i)) ->
                   skel.join $ skel.split n xs = xs
joinSplitSimple1 n xs = ?jss

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

skel.sj_nil = proof
  intros
  trivial 


skel.l2 = proof
  intros
  induction i
  rewrite sym (multZeroRightZero n)
  rewrite sym (multOneRightNeutral n)
  rewrite sym (plusZeroRightNeutral n)
  trivial
  intros
  rewrite (multRightSuccPlus n (S n__0))
  trivial


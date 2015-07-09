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
split {a} {i=Z}   _ _   = Nil
split {a} {i}     Z Nil = replicate i Nil

split {a} {i=S i0} n xs =
  let xs' : Array a (n + n * i0) = rewrite sym (lemma1 n i0) in xs
      (a1, a2) : (Array a n, Array a (n * i0)) = splitAt n xs'
    in a1 :: (skel.split n a2)


join : {a: Type} -> {i: Size} -> {j: Size} ->
       Array (Array a i) j -> Array a (j * i)
join Nil = Nil
join (x :: xs) = x ++ (skel.join xs)


iterate : {a: Type} -> {i: Size} -> {j: Size} ->
          (n: Size) -> ( {m: Size} -> Array a (i * m) -> Array a m ) ->
          Array a ((power i n) * j) -> Array a j
iterate {a} {i} {j} Z     f xs = (rewrite sym (plusZeroRightNeutral j) in xs)
iterate {a} {i} {j} (S n) f xs = iterate n f (f xs')
        where xs' = (rewrite (multAssociative i (power i n) j) in xs)


reorder : {a: Type} -> {i: Size} ->
          Array a i -> Array a i
reorder = id

transpose : {a: Type} -> {i: Size} -> {j: Size} ->
            Array (Array a i) j -> Array (Array a j) i
transpose = Data.VectType.Vect.transpose



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
             ((a,a) -> a) -> a -> {n: Size} -> Array a (n * i) -> Array a n

reducePart {a} {i} f z {n=(S Z)} = skel.reduce f z
reducePart {a} {i} f z {n=k}     =
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



Map : {a: Type} -> {b: Type} -> {i: Size} ->
      (a -> b) -> Array a i -> Array b i
Map = skel.map

Zip : {a: Type} -> {b: Type} -> {i: Size} ->
      Array a i -> Array b i -> Array (a, b) i
Zip = skel.zip

Reduce : {a: Type} -> {i: Size} ->
         ((a,a) -> a) -> a -> Array a i -> Array a 1
Reduce = skel.reduce

Split : {a: Type} -> {i: Size} ->
        (n: Size) -> Array a (n * i) -> Array (Array a n) i
Split = skel.split

Join : {a: Type} -> {i: Size} -> {j: Size} ->
       Array (Array a i) j -> Array a (j * i)
Join = skel.join

Iterate : {a: Type} -> {i: Size} -> {j: Size} ->
          (n: Size) -> ( {m: Size} -> Array a (i * m) -> Array a m ) ->
          Array a ((power i n) * j) -> Array a j
Iterate = skel.iterate

Reorder : {a: Type} -> {i: Size} ->
          Array a i -> Array a i
Reorder = skel.reorder

Transpose : {a: Type} -> {i: Size} -> {j: Size} ->
            Array (Array a i) j -> Array (Array a j) i
Transpose = skel.transpose

MapWorkgroup : {a: Type} -> {b: Type} -> {i: Size} ->
               (a -> b) -> Array a i -> Array b i
MapWorkgroup = skel.mapWorkgroup


MapLocal : {a: Type} -> {b: Type} -> {i: Size} ->
           (a -> b) -> Array a i -> Array b i
MapLocal = skel.mapLocal


MapGlobal : {a: Type} -> {b: Type} -> {i: Size} ->
            (a -> b) -> Array a i -> Array b i
MapGlobal = skel.mapGlobal


MapSeq : {a: Type} -> {b: Type} -> {i: Size} ->
         (a -> b) -> Array a i -> Array b i
MapSeq = skel.mapSeq


ToLocal : {a: Type} -> {b: Type} -> {i: Size} ->
          (a -> b) -> (a -> b)
ToLocal {i} = skel.toLocal {i=i}


ToGlobal : {a: Type} -> {b: Type} -> {i: Size} ->
           (a -> b) -> (a -> b)
ToGlobal {i} = skel.toGlobal {i=i}


ReduceSeq : {a: Type} -> {b: Type} -> {i: Size} ->
            ((a,b) -> a) -> a -> Array b i -> Array a 1
ReduceSeq = skel.reduceSeq

ReducePart : {a: Type} -> {i: Size} ->
             ((a,a) -> a) -> a -> {n: Size} -> Array a (n * i) -> Array a n
ReducePart = skel.reducePart


ReorderStride : {a: Type} -> {i: Size} ->
                (n: Size) -> Array a i -> Array a i
ReorderStride = skel.reorderStride


MapVec : {a: Type} -> {b: Type} ->
         {n: Size} -> (a -> b) -> Vector a n -> Vector b n
MapVec = skel.mapVec


SplitVec : {a: Type} -> {i: Size} ->
           (n: Size) -> Array a (n * i) -> Array (Vector a n) i
SplitVec = skel.splitVec


JoinVec : {a: Type} -> {i: Size} -> {j: Size} ->
          Array (Vector a i) j -> Vector a (j * i)
JoinVec = skel.joinVec

---------- Proofs ----------

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

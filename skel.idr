module skel

import Data.VectType

Size : Type
Size = Nat

Array : Type -> Size -> Type
Array a i = Vect i a

Vector : Type -> Size -> Type
Vector a i = Vect i a

-- lemmas

lemma1 : (n: Size) -> mult n 1 = plus n (mult n 0)
lemma1 Z = Refl
lemma1 (S k) = cong (lemma1 k)

lemma2 : (n: Size) -> (i: Size) -> mult n (S i) = plus n (mult n i)
lemma2 Z _ = Refl
lemma2 n Z = lemma1 n

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
      (n: Size) -> Array a (n * (S i)) -> Array (Array a n) (S i)
split {i=Z} n xs  = (rewrite sym (multOneRightNeutral n) in xs) :: Nil
split {a} {i} n xs = a1 :: a2
  where
    take : (n : Size) -> Array a (n + m) -> Array a n
    take Z     xs        = []
    take (S k) (x :: xs) = x :: take k xs

    take' : (n: Size) -> Array a (n + n * i) -> Array a n
    take' n = take n

    a1 : Array a n
    a1 = take' n (rewrite sym (lemma2 n i) in xs)

    a2 : Array (Array a n) (i - 1)
    a2 = (skel.split n (drop n xs))

join : {a: Type} -> {i: Size} -> {j: Size} ->
      Array (Array a i) j -> Array a (j * i)
join Nil = Nil
join (x :: xs) = x ++ (skel.join xs)

iterate : {a: Type} -> {i: Size} -> {j: Size} ->
      (n: Size) -> ( (m: Size) -> Array a (i * m) -> Array a m )
               -> Array a ((power i n) * j) -> Array a j
-- iterate Z f xs = xs

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
reducePart f z (S Z) = reduce f z
--reducePart {a} {i} f z k =
--  skel.join . skel.map (reduce f z) . skel.split {i=k} i

reorderStride : {a: Type} -> {i: Size} ->
      (n: Size) -> Array a i -> Array a i
reorderStride _ = id

mapVec : {a: Type} -> {b: Type} ->
      (n: Size) -> (a -> b) -> Vector a n -> Vector b n
mapVec _ = skel.map

splitVec : {a: Type} -> {i: Size} ->
      (n: Size) -> Array a (n * i) -> Array (Vector a n) i

joinVec : {a: Type} -> {i: Size} -> {j: Size} ->
      Array (Vector a i) j -> Vector a (j * i)
joinVec Nil = Nil
joinVec (x :: xs) = x ++ (joinVec xs)



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


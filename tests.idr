module skel.tests

import Data.VectType
import skel

%default total


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

xs' : Array Nat 2
xs'  = reducePart add 0 {n=2} {i=2} xs

xs'' : Array Nat 1
xs'' = reducePart add 0 {n=1} {i=2} xs'

--xs''' : Array Nat 1
--xs''' = iterate 2 (reducePart add 0) xs

res : Array Nat 4
res = Map add (Zip xs xs)

res1 : Array Nat 4
res1 = Join (Map (Map add) (Split {i=2} 2 (Zip xs xs)))

rule1example : Type
rule1example = res = res1

res2 : Array Nat 4
res2 =
  Join (Map f z)
  where
    z : Array (Array Nat 2, Array Nat 2) 2
    z = Zip (Split {i=2} 2 xs) (Split {i=2} 2 xs)

    f : (Array Nat 2, Array Nat 2) -> Array Nat 2
    f = \(x,y) => Map add (Zip x y)

rule2example : Type
rule2example = res = res2

xss : Array (Array Nat 4) 4
xss = [[1, 2, 3, 4],
       [1, 2, 3, 4],
       [1, 2, 3, 4],
       [1, 2, 3, 4]]

res3 : Array (Array Nat 1) 4
res3 = Map (Reduce add 0) xss

res4 : Array (Array Nat 1) 4
res4 = Join (Map (Map (Reduce add 0)) (Split {i=2} 2 xss))

rule3example : Type
rule3example = res4 = res3

res5 : Array Nat 1
res5 = Reduce add 0 xs

res6 : Array Nat 1
res6 = Reduce add 0 (Join (Reduce (\(x,y) => Map add (Zip x y)) [0,0] (Split {i=2} 2 xs)))

rule4example : Type
rule4example = res5 = res6

res7 : Array (Nat, Nat) 4
res7 = Reorder (Zip xs xs)

res8 : Array (Nat, Nat) 4
res8 = Zip (Reorder xs) (Reorder xs)

rule5example : Type
rule5example = res7 = res8

res9 : Array (Array Nat 1) 4
res9 = Map (Reduce add 0) xss

res10 : Array (Array Nat 1) 4
res10 = Transpose (Reduce (\(x,y) => Map add (Zip x y)) [0,0,0,0] (Transpose xss))

rule6example : Type
rule6example = res9 = res10

yss : Array (Array Nat 4) 4
yss = [[1, 1, 1, 1],
       [2, 2, 2, 2],
       [3, 3, 3, 3],
       [4, 4, 4, 4]]

{-
dotProd : {n: Size} -> Array Nat n -> Array Nat n -> Array Nat 1
dotProd {n=n} x y = r
  where
    z : Array (Nat,Nat) n
    z = Zip x y
    r : Array Nat 1
    r = Reduce add 0 z
-}

{-
matMultOrig : Array (Array Nat 4) 4
matMultOrig =
  Map (\arow =>
    Map (\bcol => dotProd arow bcol) B ) A
-}

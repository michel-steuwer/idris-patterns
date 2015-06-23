module interp

import Data.VectType
import Data.Fin

%default total

lemma1 : (n: Nat) -> (i: Nat) -> mult n (S i) = plus n (mult n i)
lemma1 n i = ?l2

-- Language types.
data Ty = TyFlo | TyInt | TyArray Ty Nat
        | TyTup Ty Ty | TyFun Ty Ty

-- Function from the Ty types to real Idris types.
interpTy : Ty -> Type
interpTy TyFlo = Float
interpTy TyInt = Int
interpTy (TyArray e s) = Vect s (interpTy e)
interpTy (TyTup T1 T2) = (interpTy T1, interpTy T2)
interpTy (TyFun A T) = interpTy A -> interpTy T

using (G:Vect n Ty) {

data Expr : Vect n Ty -> Ty -> Type

data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
  Stop : HasType FZ (t :: G) t
  Pop  : HasType k G t -> HasType (FS k) (u :: G) t

-- NOTE: I'm not sure how sizes should be handled.

data Expr : Vect n Ty -> Ty -> Type where

  -- Literals
  ValF    : (x : Float) -> Expr G TyFlo
  ValI    : (x : Int)   -> Expr G TyInt
  -- How should we introduce arrays into the language?
  
  -- Language forms
  Var     : HasType i G t -> Expr G t
  Lam     : Expr (a :: G) t -> Expr G (TyFun a t)
  App     : Expr G (TyFun a t) -> Expr G a -> Expr G t
  Op      : (interpTy a -> interpTy b -> interpTy c) ->
            Expr G a -> Expr G b -> Expr G c
  Map     : Expr G (TyFun a b) -> 
            Expr G (TyArray a s) -> Expr G (TyArray b s)
  Zip     : Expr G (TyArray a s) -> Expr G (TyArray b s) ->
            Expr G (TyArray (TyTup a b) s)
  Split   : (n : Nat) -> -- Should this be a plain (idris) nat?
            Expr G (TyArray a (mult n i)) ->
            Expr G (TyArray (TyArray a n) i)
  Join    : Expr G (TyArray (TyArray a i) j) ->
            Expr G (TyArray a (mult j i))
            
  -- Iterate : (n : Nat) -> -- How should the function for iterate work here?
  --           Expr G (TyFun (TyArray a (mult i m)) (TyArray a m)) ->
  --           Expr G (TyArray a (mult (power i n) j)) ->
  --           Expr G (TyArray a j)

data Env : Vect n Ty -> Type where
  Nil  : Env Nil
  (::) : interpTy a -> Env G -> Env (a :: G)

lookup : HasType i G t -> Env G -> interpTy t
lookup Stop    (x :: xs) = x
lookup (Pop k) (x :: xs) = lookup k xs

interp : Env G -> Expr G t -> interpTy t
interp env (Var i) = lookup i env
interp env (ValF x) = x
interp env (ValI x) = x
interp env (Lam sc) = \x => interp (x :: env) sc
interp env (App f s) = interp env f (interp env s)
interp env (Op op x y) = op (interp env x) (interp env y)

interp env (Map f arr) = doMap (interp env f) (interp env arr)
       where doMap : (a -> b) -> Vect n a -> Vect n b
             doMap f Nil = Nil
             doMap f (x :: xs) = (f x) :: (doMap f xs)

interp env (Zip xs1 xs2) = doZip (interp env xs1) (interp env xs2)
       where doZip : Vect n a -> Vect n b -> Vect n (a, b)
             doZip Nil Nil = Nil
             doZip (x :: xs) (y :: ys) = (x, y) :: (doZip xs ys)

interp env (Split n xs) = doSplit n (interp env xs)
       where doSplit : (n : Nat) -> Vect (mult n i) a -> 
                       Vect i (Vect n a)
             doSplit {i=Z} n (rewrite (multZeroRightZero n) in Nil) = Nil
             doSplit {i=S k} n xs = a1 :: a2
                     where take' : (n : Nat) -> Vect (plus n (mult n k)) a -> Vect n a
                           take' n = take n
                           drop' : (n : Nat) -> Vect (plus n (mult n k)) a -> Vect (mult n k) a
                           drop' n = drop n
                           a1 : Vect n a
                           a1 = take' n (rewrite sym (lemma1 n k) in xs)
                           a2 : Vect k (Vect n a)
                           a2 = doSplit n (drop' n (rewrite sym (lemma1 n k) in xs))
                           
interp env (Join xs) = doJoin (interp env xs)
       where doJoin : Vect j (Vect i a) -> Vect (mult j i) a
             doJoin Nil = Nil
             doJoin (x :: xs) = x ++ (doJoin xs)

-- interp env (Iterate n f xs) = ?evaliterate

}

interp.l2 = proof
  intros
  induction i
  rewrite sym (multZeroRightZero n)
  rewrite sym (multOneRightNeutral n)
  rewrite sym (plusZeroRightNeutral n)
  trivial
  intros
  rewrite (multRightSuccPlus n (S n__0))
  trivial

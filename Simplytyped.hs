module Simplytyped (
       conversion,    -- conversion a terminos localmente sin nombre
       eval,          -- evaluador
       infer,         -- inferidor de tipos
       quote          -- valores -> terminos
       )
       where

import Data.List
import Data.Maybe
import Prelude hiding ((>>=))
import Text.PrettyPrint.HughesPJ (render)
import PrettyPrinter
import Common

-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion = conversion' []

conversion' :: [String] -> LamTerm -> Term
conversion' b (LVar n)         = maybe (Free (Global n)) Bound (n `elemIndex` b)
conversion' b (App t u)        = conversion' b t :@: conversion' b u
conversion' b (Abs n t u)      = Lam t (conversion' (n:b) u)
conversion' b (LLet x v e)     = Let (conversion' b v) (conversion' (x:b) e)
conversion' b (LAs t t')       = As (conversion' b t) t'
conversion' b LUnit            = Unit
conversion' b (LPair t t')     = Pair (conversion' b t) (conversion' b t')
conversion' b (LFirst t)       = First (conversion' b t)
conversion' b (LSecond t)      = Second (conversion' b t)
conversion' b LZero            = Zero
conversion' b (LSucc t)        = Succ (conversion' b t)
conversion' b (LRec t t' t'')  = Rec (conversion' b t) (conversion' b t') (conversion' b t'')


-----------------------
--- eval
-----------------------

sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n)              = Free n
sub i t (u :@: v)             = sub i t u :@: sub i t v
sub i t (Lam t' u)            = Lam t' (sub (i+1) t u)
sub i t (Let t' u)            = Let (sub i t t') (sub (i+1) t u)
sub i t (As t' u)             = As (sub i t t') u
sub i t Unit                  = Unit
sub i t (Pair t' t'')         = Pair (sub i t t') (sub i t t'')
sub i t (First t')            = First (sub i t t')
sub i t (Second t')           = Second (sub i t t')
sub i t Zero                  = Zero
sub i t (Succ t')             = Succ (sub i t t')
sub i t (Rec t' t'' t''')     = Rec (sub i t t') (sub i t t'') (sub i t t''')


-- evaluador de términos
eval :: NameEnv Value Type -> Term -> Value
eval _ (Bound _)             = error "variable ligada inesperada en eval"
eval e (Free n)              = fst $ fromJust $ lookup n e
eval _ (Lam t u)             = VLam t u
eval e (Lam _ u :@: Lam s v) = eval e (sub 0 (Lam s v) u)
eval e (Lam t u :@: v)       = let t' = eval e v in eval e (sub 0 (quote t') u)
eval e (u :@: v)             = case eval e u of
                 VLam t u'  -> eval e (Lam t u' :@: v)
                 _          -> error "Error de tipo en run-time, verificar type checker - 1"
eval e (Let t u)             = let t' = eval e t in eval e (sub 0 (quote t') u)
eval e (As t t')             = eval e t
eval e Unit                  = VUnit
eval e (Pair t t')           = VPair (eval e t) (eval e t')
eval e (First t)             = case eval e t of
                VPair t' _  -> t' 
                _           -> error "Error de tipo en run-time, verificar type checker - 2"
eval e (Second t)            = case eval e t of
                VPair _ t'  -> t' 
                _           -> error "Error de tipo en run-time, verificar type checker - 3"
eval e Zero                  = VNat NatZero
eval e (Succ t)              = case eval e t of
                VNat x -> VNat (NatSucc x)
                _ -> error "Error de tipo en run-time, verificar type checker - 4"
eval e (Rec t u v)           = case eval e v of
                VNat NatZero     -> eval e t
                VNat (NatSucc x) -> let tq = quote (VNat x)
                                    in eval e (u :@: (Rec t u tq) :@: tq)
                _ -> error "Error de tipo en run-time, verificar type checker - 5"


-----------------------
--- quoting
-----------------------

quote :: Value -> Term
quote (VLam t f)         = Lam t f
quote VUnit              = Unit
quote (VPair t t')       = Pair (quote t) (quote t')
quote (VNat NatZero)     = Zero
quote (VNat (NatSucc x)) = Succ (quote (VNat x))


----------------------
--- type checker
-----------------------

-- type checker
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=) :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error

matchError :: Type -> Type -> Either String Type
matchError t1 t2 = err $ "se esperaba " ++
                         render (printType t1) ++
                         ", pero " ++
                         render (printType t2) ++
                         " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free n) = case lookup n e of
                        Nothing -> notfoundError n
                        Just (_,t) -> ret t
infer' c e (t :@: u) = infer' c e t >>= \tt -> 
                       infer' c e u >>= \tu ->
                       case tt of
                         Fun t1 t2 -> if (tu == t1) 
                                        then ret t2
                                        else matchError t1 tu
                         _         -> notfunError tt
infer' c e (Lam t u) = infer' (t:c) e u >>= \tu ->
                       ret $ Fun t tu
infer' c e (Let t u) = infer' c e t >>= \t' ->
                       infer' (t':c) e u
infer' c e (As t t') = infer' c e t >>= \q ->
                        if t' == q
                        then ret t'
                        else matchError t' q
infer' c e Unit      = ret TypeUnit                        
infer' c e (Pair t t') = infer' c e t >>= \t1 ->
                         infer' c e t' >>= \t2 ->
                         ret $ TypePair t1 t2
infer' c e (First t)   = infer' c e t >>= \t1 ->
                        case t1 of 
                         TypePair t' _ -> ret t'
                         t' -> err $ "se esperaba una tupla, pero " 
                                    ++ render (printType t')
                                    ++ " fue inferido."
infer' c e (Second t)  = infer' c e t >>= \t1 ->
                        case t1 of 
                         TypePair _ t' -> ret t'
                         t' -> err $ "se esperaba una tupla, pero " 
                                    ++ render (printType t')
                                    ++ " fue inferido."
infer' c e Zero        = ret TypeNat
infer' c e (Succ t)    = infer' c e t >>= \t' ->
                        case t' of
                         TypeNat -> ret t'
                         _ -> err $ "se esperaba un natural, pero "
                                    ++ render (printType t')
                                    ++ " fue inferido."
infer' c e (Rec t t' t'') = infer' c e t >>= \t1 ->
                            infer' c e t' >>= \t2 ->
                            infer' c e t'' >>= \t3 ->
                        case t3 of
                         TypeNat -> if t2 == Fun t1 (Fun TypeNat t1)
                                    then ret t1
                                    else matchError (Fun t1 (Fun TypeNat t1)) t2
                         _ -> err $ "se esperaba un natural, pero "
                                    ++ render (printType t3)
                                    ++ " fue inferido."


     
----------------------------------

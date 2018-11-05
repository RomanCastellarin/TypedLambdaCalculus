module PrettyPrinter (
       printTerm,     -- pretty printer para terminos
       printType,     -- pretty printer para tipos
       )
       where

import Common
import Text.PrettyPrint.HughesPJ

-- lista de posibles nombres para variables
vars :: [String]
vars = [ c : n | n <- "" : map show [(1::Integer)..], c <- ['x','y','z'] ++ ['a'..'w'] ]
              
parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-- pretty-printer de términos

pp :: Int -> [String] -> Term -> Doc
pp ii vs (Bound k)         = text (vs !! (ii - k - 1))
pp _  _  (Free (Global s)) = text s

pp ii vs (i :@: c) = sep [parensIf (isLam i) (pp ii vs i), 
                          nest 1 (parensIf (isLam c || isApp c) (pp ii vs c))]  
pp ii vs (Lam t c) = text "\\" <>
                     text (vs !! ii) <>
                     text ":" <>
                     printType t <>
                     text ". " <> 
                     pp (ii+1) vs c
pp ii vs (Let t c) = text "let " <>
                     text (vs !! ii) <>
                     text " = " <>
                     pp ii vs t <>
                     text " in " <> 
                     pp (ii+1) vs c
pp ii vs (As t t') = pp ii vs t <>
                     text " as " <>
                     printType t'
pp ii vs Unit      = text "unit"
pp ii vs (Pair t t')  = text "(" <>
                        pp ii vs t <>
                        text ", " <>
                        pp ii vs t' <>
                        text ")"
pp ii vs (First t) = text "fst " <> 
                     pp ii vs t 
pp ii vs (Second t) = text "snd " <> 
                     pp ii vs t 
pp ii vs Zero = text "0 "
pp ii vs (Succ t) = text "succ "<>
                    pp ii vs t
pp ii vs (Rec t1 t2 t3) = sep [ text "R " ,
                                parensIf (not $ isAtom t1) (pp ii vs t1) ,
                                parensIf (not $ isAtom t2) (pp ii vs t2) ,
                                parensIf (not $ isAtom t3) (pp ii vs t3)
                                ]
                     
isLam :: Term -> Bool                    
isLam (Lam _ _) = True
isLam  _      = False

isApp :: Term -> Bool        
isApp (_ :@: _) = True
isApp _         = False 

isAtom :: Term -> Bool
isAtom t = case t of
             Free _   -> True
             Bound _  -> True
             Unit     -> True
             Zero     -> True
             Pair _ _ -> True
             _        -> False

-- pretty-printer de tipos
printType :: Type -> Doc
printType Base         = text "B"
printType TypeUnit     = text "Unit"
printType TypeNat      = text "Nat"
printType (TypePair t1 t2) = text "(" <>
                        printType t1 <>
                        text ", " <>
                        printType t2 <>
                        text ")"
printType (Fun t1 t2)  = sep [ parensIf (isFun t1) (printType t1), 
                               text "->", 
                               printType t2]

isFun :: Type -> Bool
isFun (Fun _ _)        = True
isFun _                = False

fv :: Term -> [String]
fv (Bound _)         = []
fv (Free (Global n)) = [n]
fv (t :@: u)         = fv t ++ fv u
fv (Lam _ u)         = fv u
fv (Let t u)         = fv t ++ fv u
fv (As t _)          = fv t
fv (First t)         = fv t
fv (Second t)        = fv t
fv Unit              = []
fv (Pair t u)        = fv t ++ fv u
fv Zero              = []
fv (Succ t)          = fv t
fv (Rec t u v)       = fv t ++ fv u ++ fv v
  
---
printTerm :: Term -> Doc 
printTerm t = pp 0 (filter (\v -> not $ elem v (fv t)) vars) t


{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
import           Text.PrettyPrint
import qualified Data.Map as Map

import           ConstraintSolver

main :: IO ()
main = test defs eqs
  where
  defs          = [ dPlus cZero     a  $  a
                  , dPlus (cSucc a) b  $  cSucc (fPlus a b)
                  ]

  eqs           = [ fPlus a b :=: b, fPlus a b :=: cZero ]

  cZero         = TCon "Zero"
  cSucc t       = TCon "Succ" `TApp` t
  dPlus p q r   = TFunDef "Plus" [p,q] r
  fPlus p q     = TFun "Plus" [p,q]

  a : b : _     = map TVar [ "a", "b", "c" ]




test :: [TFunDef] -> [Eqn Type] -> IO ()
test defs eqs =
  case normalize "$" defs eqs of
    Nothing -> putStrLn "(inconsistent)"
    Just s  -> print (pp s)





--------------------------------------------------------------------------------
-- Pretty Printing for Testing

class PP t where
  pp :: t -> Doc

instance PP Type where
  pp ty = case ty of
            TVar x      -> text x
            TCon c      -> text c
            TFun f ts   -> text f <+> hsep (map wrapTy ts)
            TApp t1 t2  -> pp t1 <+> wrapTy  t2

wrapTy :: Type -> Doc
wrapTy sty = case sty of
               TVar _    -> pp sty
               TCon _    -> pp sty
               TFun _ [] -> pp sty
               TFun _ _  -> parens (pp sty)
               TApp _ _  -> parens (pp sty)

instance PP Subst where
  pp su
    | Map.null su = text "(empty)"
    | otherwise   = vcat [ text x <+> text ":=" <+> pp y
                                                | (x,y) <- Map.toList su ]

instance PP TFunEqn where
  pp (TFunEqn f ts t) = text f <+> hsep (map wrapTy ts) <+> text "~" <+> pp t

instance PP Inerts where
  pp is = vcat [ text "inert substitution:"
               , nest 2 (pp (inertSubst is))
               , text "inert equations:"
               , nest 2 (ppList (inertFuns is))
               ]

instance PP t => PP (Eqn t) where
  pp (t1 :=: t2) = pp t1 <+> text "~" <+> pp t2

instance PP WorkQueue where
  pp q = vcat [ text "simple equations:"
              , nest 2 (ppList (simpleEqns q))
              , text "function equations:"
              , nest 2 (ppList (tfunEqns q))
              ]

ppList :: PP a => [a] -> Doc
ppList [] = text "(empty)"
ppList xs = vcat (map pp xs)


instance PP TFunDef where
  pp (TFunDef f ts t) = text "type instance" <+> text f <+>
                        hsep (map wrapTy ts) <+> text "=" <+> pp t

instance PP State where
  pp s = text "-- State ---" $$ pp (inerts s) $$ pp (canEqs s)

instance PP Doc where
  pp = id





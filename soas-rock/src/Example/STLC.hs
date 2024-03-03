{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Example.STLC where

import Free.Scoped (AnnF (AnnF), FS (Free, Pure), Inc (..),
                                    substitute, untyped)
import Free.Scoped.TH (makePatternsAll)
import Data.Bifunctor.TH
    ( deriveBifoldable, deriveBifunctor, deriveBitraversable )

data TermF scope term
  = AppF term term       -- (T₁ T₂)
  | AbsF term scope      -- λx:T. t
  | TypeFunF term term   -- T₁ → T₂
  | TypeBaseF            -- B
  deriving (Eq, Show, Functor, Foldable, Traversable)
deriveBifunctor ''TermF
deriveBifoldable ''TermF
deriveBitraversable ''TermF
-- This generates pattern synonyms to give us back convenient constructors, as well as their typed (annotated) variants
makePatternsAll ''TermF

type Term = FS TermF

-- | This will be considered the type of the "annotation" attached to terms.
-- It can include more than just the type information (e.g.: definition location).
-- `term` is whatever our representation of types is.
-- In this case, we use the same data type as terms, just with different constructors.
newtype TypeInfo term = TypeInfo
  { typeInfo :: term }
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- TermT constructors are basically the same constructors of Term but with an additional first argument: TypeInfo
type TermT = FS (AnnF TypeInfo TermF)

-- | Weak head normal form (evaluate until the outermost abstraction)
whnf :: Term a -> Term a
whnf = \case
  App fun arg ->
    case whnf fun of
      Abs _paramType body -> whnf (substitute arg body)
      fun'                -> App fun' arg
  term -> term

-- * Some Examples
--
-- $examples
-- To better understand how to simply-type lambda calculus with second order abstract syntax
-- In `Term a`, `a` is the type of **free** variables

-- | λx:B. x  = λ0
identity :: Term a
identity = Abs TypeBase (Pure Z)

-- | λf: (B -> B) . λx:B. f x  =  λ1 0
-- Note that the type itself does not allow referencing free variables!
churchOne :: Term a
churchOne = Abs (TypeFun TypeBase TypeBase) (Abs TypeBase (App (Pure (S Z)) (Pure Z)))

-- | λn f x. f (n f x)  =  λ1 (2 1 0)
--
-- >>> whnf (App churchSucc churchOne)
-- Free (AbsF (Free (AbsF (Free (AppF (Pure (S Z)) (Free (AppF (Free (AppF (Free (AbsF (Free (AbsF (Pure Z))))) (Pure (S Z)))) (Pure Z))))))))
churchSucc :: Term a
churchSucc = Abs TypeBase (Abs TypeBase (Abs TypeBase (App f (App (App n f) x))))
  where
    x = Pure Z
    f = Pure $ S Z
    n = Pure $ S (S Z)

churchTwo :: Term a
churchTwo = whnf (App churchSucc churchOne)

-- * Utility functions

-- >>> prettyPrint churchTwo
-- "\955:B. \955:B. (S Z ((\955:B. \955:B. (S Z Z) S Z) Z))"
prettyPrint :: [String] -> Term String -> String
prettyPrint freshVars (Abs paramType body) =
  case freshVars of
    new : moreFreshVars -> "λ " <> new <> ":" ++ prettyPrint freshVars paramType  ++ ". " ++ prettyPrint moreFreshVars (renameWith new body)
    [] -> error "not enough fresh variables!"
prettyPrint freshVars (App f body) = "(" ++ prettyPrint freshVars f ++ " " ++ prettyPrint freshVars body ++ ")"
prettyPrint freshVars (TypeFun paramType returnType) = "(" ++ prettyPrint freshVars paramType ++ ")" ++ " -> " ++ prettyPrint freshVars returnType
prettyPrint _freshVars TypeBase = "B"
prettyPrint _freshVars (Pure var) = var

defaultVars :: [String]
defaultVars = map pure ['a'..'z'] <> [ "x" <> show index | index <- [(1 :: Int)..] ]

pp :: Show a => Term a -> String
pp = prettyPrint defaultVars . fmap show

ppT :: Show a => TermT a -> String
ppT t = case t of
  Pure{}                      -> pp (untyped t)
  Free (AnnF (TypeInfo ty) _) -> pp (untyped t) <> " : " <> pp (untyped ty)

-- typecheck :: Term a -> TermT a -> TypeCheck (TermT a)

{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Example.STLC where

import Free.Scoped ( substitute, FS, AnnF )
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
makePatternsAll ''TermF

type Term = FS TermF

newtype TypeInfo term = TypeInfo
  { typeInfo :: term }
  deriving (Eq, Show, Functor, Foldable, Traversable)

type TermT = FS (AnnF TypeInfo TermF)

whnf :: Term a -> Term a
whnf = \case
  App fun arg ->
    case whnf fun of
      Abs _paramType body -> whnf (substitute arg body)
      fun'                -> App fun' arg
  term -> term

-- typecheck :: Term a -> TermT a -> TypeCheck (TermT a)

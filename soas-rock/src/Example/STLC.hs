{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}

module Example.STLC where

import           Data.Bifunctor
import           Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor,
                                    deriveBitraversable)
import           Free.Scoped       (AnnF (AnnF), FS (Free, Pure), Inc (..),
                                    substitute, untyped)
import           Free.Scoped.TH    (makePatternsAll)

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
--
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


-- * Typechecking
--
-- $typechecking
-- To keep things as simple as possible, the forbidden `error` is used instead of `Either`
-- or some other monad. In a real-life example, some monad (such as ReaderT) would likely
-- be used to keep the computation context and handle errors better.
--
-- A possible definition for the AST that includes a self-containing universe type could be like so:
--
-- @
--    data TermF ...
--        = ...
--        | UniverseF
--
--    universeT :: TermT a
--    universeT = UniverseT (TypeInfo universeT)
-- @

-- | Types table (indexed by our representation of free vars).
-- A more realistic scenario would probably use something like:
--
-- @
--    data VarInfo a = VarInfo -- include type, usage sites, definition location, ...
--    newtype Context a = Context [(a, VarInfo a)]
-- @
type Context a = [(a, TermT a)]


-- ** Helper functions

-- | Given a new name for the variable and a term in an incremented scope,
-- renames the innermost variable to the provided name and decrements the scope
renameWith :: a -> Term (Inc a) -> Term a
renameWith new = fmap $ \case
  Z -> new
  S x -> x


-- ** Types as typed terms (TermT)

-- | TypeBase as a typed term
typeBaseT :: TermT a
-- since we don't have self-containing types (or types/kinds of types), the type of Base is undefined (or error)
typeBaseT = TypeBaseT (TypeInfo (error "typeBaseT: undefined"))

-- | The type of a function (not a typed function!).
-- There should probably be a distinction between them on the type-level
-- (of the Haskell source code), but let's keep it simple.
typeFunT :: TermT a -> TermT a -> TermT a
-- Again undefined because no type of type
typeFunT = TypeFunT (TypeInfo (error "typeFunT: undefined"))


-- ** Typed terms (terms with attached type info)

-- | Typed application (an application that knows its type).
-- Assumes both terms are already typechecked.
-- @(x y)@
appT :: (Eq a) => Context a -> TermT a -> TermT a -> TermT a
appT ctx t1 t2 = case typeOf extractType t1 of
  TypeFunT _ _paramType retType -> AppT (TypeInfo retType) t1 t2
  _                             -> error "Not a function"
  where
    extractType var = case lookup var ctx of
      Just type_ -> type_
      Nothing    -> error "undefined variable"

-- | Typed abstraction.
-- Given the parameter type and return type (whose scope is incremented because it's the function body),
-- constructs the type information of such function.
absT :: TermT a -> TermT (Inc a) -> TermT a
-- (const (fmap S paramType)) because type variables are not supported, so no need to lookup variables
absT paramType body = AbsT (TypeInfo $ typeFunT paramType (nonDep (typeOf (const (fmap S paramType)) body))) paramType body

-- | Ensures that we do not have dependent typing and decrements the scope
nonDep :: TermT (Inc a) -> TermT a
nonDep = fmap $ \case
  Z -> error "Dependent type! AAHHHH!"
  S x -> x


-- ** Typechecking

-- | Verify that the given argument is a type (an AST node representing a well-formed type)
checkType :: Term a -> TermT b
checkType TypeBase = typeBaseT
checkType (TypeFun paramType bodyType) = typeFunT (checkType paramType) (checkType bodyType)
checkType _ = error "Not a type"

-- | Given some context, a term to be typechecked, and possibly an expected type from this term,
-- check that the term is well-typed and return the actual inferred type for it.
typecheck :: (Eq a) => Context a -> Term a -> Maybe (TermT a) -> TermT a
typecheck ctx (Pure var) expectedType = case lookup var ctx of
  Just t
    | Just ex <- expectedType -> if t == ex then t else error "unexpected type"
    | otherwise -> t
  Nothing -> error "undefined variable"
typecheck ctx (Abs paramType body) expectedType = case expectedType of
  Just (TypeFunT _ expectedParamType bodyType)
    | paramTypeT == expectedParamType -> absT paramTypeT $ typecheck extendedCtx body (Just (fmap S bodyType))
    | otherwise -> absT paramTypeT $ typecheck extendedCtx body Nothing
  Just _ -> error "Unexpected abstraction"
  Nothing -> error "Unexpected param type"
  where
    paramTypeT = checkType paramType
    extendedCtx = (Z, paramTypeT) : map (bimap S (fmap S)) ctx
typecheck ctx (App f arg) expectedType
  | typesMatch = returnType
  | otherwise = error "Invalid application"
  where
    funType = typecheck ctx f Nothing
    (paramType, returnType) = case funType of
       (TypeFunT _ param ret) -> (param, ret)
       _                      -> error "Not a function"
    argType = typecheck ctx arg (Just paramType)
    typesMatch = paramType == argType && expectedType == Just returnType
typecheck _ctx _expr _type = error "Unexpected type for expression"

-- | Given a context and an untyped term, try to infer a type for this term and attach it to it.
infer :: (Eq a) => Context a -> Term a -> TermT a
infer ctx (Abs paramType body) = absT paramTypeT (infer extendedCtx body)
  where
    paramTypeT = checkType paramType
    extendedCtx = (Z, fmap S paramTypeT) : map (bimap S (fmap S)) ctx
infer ctx (App t1 t2)          = appT ctx (infer ctx t1) (infer ctx t2)
infer ctx (Pure var)           = case lookup var ctx of
  Just _  -> Pure var
  Nothing -> error "undefined variable"
-- Types of types are not supported
infer _ctx TypeBase{} = error "trying to infer a type of TypeBase"
infer _ctx TypeFun{} = error "trying to infer a type of a function type (TypeFun)"

-- | Extracts the type from an already typed term.
-- The only reason both are the same "TermT" type is that we use different constructors of the same type.
-- The first argument is the "type map" of free variables.
typeOf :: (a -> TermT a) -> TermT a -> TermT a
typeOf _ (AbsT (TypeInfo type_) _paramType _body) = type_
typeOf _ (AppT (TypeInfo type_) _t1 _t2)          = type_
typeOf extractType (Pure var)                     = extractType var
typeOf _ TypeFunT{}          = error "trying to extract a type of a function type (TypeFun)"
typeOf _ TypeBaseT{} =           error "trying to extract a type of TypeBase"

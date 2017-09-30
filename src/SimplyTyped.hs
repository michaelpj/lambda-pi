module SimplyTyped where

import Control.Monad

data TermI
  = Ann TermC Type
  | Bound Int
  | Free Name
  | TermI :@: TermC
  deriving (Show, Eq)

data TermC
  = Inf TermI
  | Lam TermC
  deriving (Show, Eq)

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

data Type
  = TFree Name
  | Fun Type Type
  deriving (Show, Eq)

data Value
  = VLam (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApp Neutral Value

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

vapp :: Value -> Value -> Value
vapp v v' = case v of
  VLam f -> f v'
  VNeutral n -> VNeutral (NApp n v')

type Env = [Value]

evalI :: TermI -> Env -> Value
evalI t env = case t of
  Ann e _ -> evalC e env
  Bound i -> env !! i
  Free x -> vfree x
  e :@: e' -> vapp (evalI e env) (evalC e' env)

evalC :: TermC -> Env -> Value
evalC t env = case t of
  Inf e -> evalI e env
  Lam e -> VLam (\v -> evalC e (v : env))

-- Type checking
type Result a = Either String a
throwError :: String -> Result a
throwError s = Left s

data Kind
  = Star
  deriving (Show)

data Info
  = HasKind Kind
  | HasType Type
  deriving (Show)

type Context = [(Name, Info)]

kindC :: Context -> Type -> Kind -> Result ()
kindC g (TFree x) Star = case lookup x g of
  Just (HasKind Star) -> return ()
  _ -> throwError "Unknown identifier"
kindC g (Fun k k') Star = do
  kindC g k Star
  kindC g k' Star

typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0

typeI :: Int -> Context -> TermI -> Result Type
typeI i g (Ann e t) = do
  kindC g t Star
  typeC i g e t
  return t
typeI i g (Free x) = case lookup x g of
  Just (HasType t) -> return t
  _ -> throwError "Unknown identifier"
typeI i g (e :@: e') = do
  s <- typeI i g e
  case s of
    Fun t t' -> do
      typeC i g e' t
      return t'
    _ -> throwError "Illegal application"
typeI i g (Bound _) = throwError "Impossible"

typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i g (Inf e) t = do
  t' <- typeI i g e
  unless (t==t') (throwError "Type mismatch")
typeC i g (Lam e) (Fun t t') =
  typeC (i+1) ((Local i, HasType t) : g) (substC 0 (Free (Local i)) e) t'
typeC _ _ _ _ = throwError "Type mismatch"

substI :: Int -> TermI -> TermI -> TermI
substI i r (Ann e t) = Ann (substC i r e) t
substI i r (Bound j) = if i==j then r else Bound j
substI _ _ (Free y) = Free y
substI i r (e :@: e') = (substI i r e) :@: (substC i r e')

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i+1) r e)

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote i (VLam f) = Lam (quote (i+1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = (neutralQuote i n) :@: quote i v

boundfree :: Int -> Name -> TermI
boundfree i (Quote k) = Bound (i-k-1)
boundfree i x = Free x

-- Testing
id' = Lam (Inf (Bound 0))
const' = Lam (Lam (Inf (Bound 1)))
tfree a = TFree (Global a)
free x = Inf (Free (Global x))

term1 = Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"
term2 = Ann const' (Fun (Fun (tfree "b") (tfree "b")) (Fun (tfree "a") (Fun (tfree "b") ((tfree "b"))))) :@: id' :@: free "y"

env1 = [(Global "y", HasType (tfree "a")), (Global "a", HasKind Star)]
env2 = [(Global "b", HasKind Star)] ++ env1

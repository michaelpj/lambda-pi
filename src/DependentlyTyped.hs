module DependentlyTyped where

import Control.Monad

data TermI
  = Ann TermC TermC
  | Star
  | Pi TermC TermC
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

data Value
  = VLam (Value -> Value)
  | VStar
  | VPi Value (Value -> Value)
  | VNeutral Neutral

type Type = Value

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
  Star -> VStar
  Pi t t' -> VPi (evalC t env) (\x -> evalC t' (x : env))

evalC :: TermC -> Env -> Value
evalC t env = case t of
  Inf e -> evalI e env
  Lam e -> VLam (\v -> evalC e (v : env))

-- Type checking
type Result a = Either String a

throwError :: String -> Result a
throwError s = Left s

type Context = [(Name, Type)]

typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0

typeI :: Int -> Context -> TermI -> Result Type
typeI i g (Ann e p) = do
  typeC i g p VStar
  let t = evalC p []
  typeC i g e t
  return t
typeI i g Star = return VStar
typeI i g (Pi p p') = do
  typeC i g p VStar
  let t = evalC p []
  typeC (i+1) ((Local i, t):g) (substC 0 (Free (Local i)) p') VStar
  return VStar
typeI i g (Free x) = case lookup x g of
  Just t -> return t
  _ -> throwError "Unknown identifier"
typeI i g (e :@: e') = do
  s <- typeI i g e
  case s of
    VPi t t' -> do
      typeC i g e' t
      return (t' (evalC e' []))
    _ -> throwError "Illegal application"
typeI i g (Bound _) = throwError "Impossible"

typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i g (Inf e) t = do
  t' <- typeI i g e
  unless (quote0 t == quote0 t') (throwError "Type mismatch")
typeC i g (Lam e) (VPi t t') =
  typeC (i+1) ((Local i, t) : g) (substC 0 (Free (Local i)) e) (t' (vfree (Local i)))
typeC _ _ _ _ = throwError "Type mismatch"

substI :: Int -> TermI -> TermI -> TermI
substI i r (Ann e t) = Ann (substC i r e) (substC i r t)
substI i r (Bound j) = if i==j then r else Bound j
substI _ _ (Free y) = Free y
substI i r (e :@: e') = (substI i r e) :@: (substC i r e')
substI i r Star = Star
substI i r (Pi t t') = Pi (substC i r t) (substC (i+1) r t')

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i+1) r e)

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote i (VLam f) = Lam (quote (i+1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)
quote i VStar = Inf Star
quote i (VPi v f) = Inf (Pi (quote i v) (quote (i+1) (f (vfree (Quote i)))))

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = (neutralQuote i n) :@: quote i v

boundfree :: Int -> Name -> TermI
boundfree i (Quote k) = Bound (i-k-1)
boundfree i x = Free x

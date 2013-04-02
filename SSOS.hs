module SSOS where 

import AST

import Data.Maybe
import Control.Concurrent
import Control.Concurrent.MVar
type Expr = Proof

type VVar = MVar Value

data Value = VOne | VUnit | VVar Int | VMPair Expr Expr
           | VAPair Expr Expr | VLam Int Expr
           | VAbort Expr {- ??? Iunno if this is even remotely right -} 
           | VInl Expr | VInr Expr
           deriving Show

data Cont = CPi1 | CPi2 | CLetOne Expr
          | CLetPair Expr
          | CApp Expr | CCase Int Expr Int Expr

eval :: Expr -> VVar -> [(Int,VVar)] -> IO ()
-- let's do all the easy ones first!! :-P
eval (Var i) x is = do 
             v <- takeMVar $ fromJust $ lookup i is
             putMVar x v
eval One x is = putMVar x VOne
eval Unit x is = putMVar x VUnit
eval (Inl e _) x is = putMVar x (VInl e)
eval (Inr _ e) x is = putMVar x (VInr e)
eval (MPair e1 e2) x is = putMVar x (VMPair e1 e2)
eval (APair e1 e2) x is = putMVar x (VAPair e1 e2)
eval (Lam i _ e) x is = putMVar x (VLam i e)
eval (Abort _ _) x is = undefined -- yyyyeah not sure what to do about this one
-- now for the things that actually involve continuations
eval (Pi1 e) x is = do y <- newEmptyMVar 
                       forkIO (eval e y is)
                       v <- takeMVar y 
                       case v of
                         VAPair e1 e2 -> eval e1 x is
                         _ -> error "type error in pi1"
eval (Pi2 e) x is = do y <- newEmptyMVar
                       forkIO (eval e y is)
                       v <- takeMVar y
                       case v of
                         VAPair e1 e2 -> eval e2 x is
                         _ -> error "type error in pi2"
eval (App e1 e2) x is = do y <- newEmptyMVar 
                           forkIO (eval e1 y is)
                           v <- takeMVar y
                           case v of
                             VLam i ef -> do
                                       z <- newEmptyMVar
                                       forkIO (eval e2 z is)
                                       eval ef x ((i, z) : is)
-- need to finish the other cases basically everything should follow this
-- continued pattern of forking, taking, and creating fresh variables
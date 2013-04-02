module AST where

import Control.Monad
import Data.List
import Data.Maybe

type TEnv = [(Int,Prop)]

data Prop = P1
          | P0
          | PTop
          | PSum Prop Prop 
          | Prop :&: Prop
          | Prop :*: Prop
          | Prop :+: Prop
          | Prop :->: Prop
          deriving (Eq, Show)

data Proof = Var Int
           | One
           | Unit
           | Inl Proof Prop
           | Inr Prop Proof
           | MPair Proof Proof
           | APair Proof Proof
           | Pi1 Proof
           | Pi2 Proof
           | Case Proof Int Proof Int Proof
           | Lam Int Prop Proof
           | App Proof Proof
           | LetPair Proof Int Int Proof
           | LetOne Proof Proof
           | Abort Prop Proof
           deriving Show
-- doing the typechecking involves splitting the context in some cases: honestly, that can just be a simple stupid backtracking

splitter :: TEnv -> [(TEnv,TEnv)]
splitter xs = map (\ i -> splitAt i xs) [0..length xs]

allContexts :: TEnv -> [(TEnv,TEnv)]
allContexts ts = concatMap splitter $ permutations ts

grabJust :: [Maybe a] -> Maybe a
grabJust xs = case catMaybes xs of
                [] -> Nothing
                y -> Just (head y)

typeAux term1 term2 = typeAux' (\ ts1 ts2 -> do
                                   prop1 <- typechecker ts1 term1
                                   prop2 <- typechecker ts2 term2
                                   return $ (prop1, prop2))

typeAux' f ts = grabJust $ map (uncurry f) $ allContexts ts

typechecker :: TEnv -> Proof -> Maybe Prop
typechecker [(v,p)] (Var i) = if v == i then return p else Nothing
typechecker delta (Var i) = Nothing
typechecker delta (Case pd vl pl vr pr) = 
  typeAux' (\ delta1 delta2 -> do
               propd <- typechecker delta1 pd
               case propd of 
                 propl :+: propr -> do 
                   prop1 <- typechecker ((vl, propl) : delta2) pl 
                   prop2 <- typechecker ((vr , propr) : delta2) pr
                   if prop1 == prop2 then Just prop1 else Nothing
                 _ -> Nothing) delta
typechecker [] One = Just P1
typechecker delta Unit = Just PTop
typechecker delta (Pi1 p) = do
                      prop <- typechecker delta p 
                      case prop of
                        p1 :&: p2 -> Just p1 
                        _ -> Nothing
typechecker delta (Pi2 p) = do
                      prop <- typechecker delta p
                      case prop of
                        p1 :&: p2 -> Just p2
                        _ -> Nothing
typechecker delta (APair p1 p2) = do
                               prop1 <- typechecker delta p1
                               prop2 <- typechecker delta p2
                               return $ prop1 :&: prop2
typechecker delta (MPair p1 p2) = do
                        (prop1, prop2) <- typeAux p1 p2 delta   
                        return $ prop1 :*: prop2
typechecker delta (LetOne p1 p2) = do
                        (prop1, prop2) <- typeAux p1 p2 delta
                        case prop1 of
                          P1 -> return prop2
                          _ -> Nothing
typechecker delta (Inl p prop) = do
                         prop'   <- typechecker delta p
                         return $ prop' :+: prop
typechecker delta (Inr prop p) = do
                         prop' <- typechecker delta p 
                         return $ prop :+: prop'
typechecker delta (Abort prop p) = 
  typeAux' (\ delta1 _ -> do
               prop1 <- typechecker delta1 p 
               case prop1 of
                 P0 -> return prop
                 _ -> Nothing) delta
typechecker delta (LetPair p1 v1 v2 p2) = 
  typeAux' (\ delta1 delta2 -> do
                prop1 <- typechecker delta1 p1
                case prop1 of 
                  prop1' :*: prop2' -> typechecker ((v1, prop1') : (v2, prop2') : delta2) p2
                  _ -> Nothing
            ) delta
typechecker delta (Lam v prop p) = do 
                          prop' <- typechecker (( v , prop) : delta) p
                          return $ prop :->: prop'
typechecker delta (App p1 p2) = 
  typeAux' (\ delta1 delta2 -> do
                prop1 <- typechecker delta1 p1
                proparg <- typechecker delta2 p2
                case prop1 of
                  prop1' :->: prop2' -> 
                    if prop1 == prop1' then return prop2' else Nothing
                  _ -> Nothing) delta
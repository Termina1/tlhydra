module TL.Typechecker.TypeholeFiller

import Effects
import Effect.State
import Effect.Exception
import Effect.StdIO

import TL.Store.Store
import TL.Types
import TL.Typechecker.TypeUnifier

mapType : TLSArg -> (TLSTypeExpr -> TEff TLSTypeExpr) -> TEff TLSArg
mapType (MkTLSArg id var_num type) f = pure (MkTLSArg id var_num !(f type))
mapType (MkTLSArgOpt id var_num type) f = pure (MkTLSArgOpt id var_num !(f type))
mapType (MkTLSArgCond id var_num cond type) f = pure (MkTLSArgCond id var_num cond !(f type))

mutual
  fillHoleExpr : TLSExpr -> TEff TLSExpr
  fillHoleExpr (MkTLSExprType type) = pure $ MkTLSExprType !(fillHoleType type)
  fillHoleExpr (MKTLSExprNat natExpr) = pure $ MKTLSExprNat natExpr

  fillHoleType : TLSTypeExpr -> TEff TLSTypeExpr
  fillHoleType (MkTLSTypeExpr type children) = do cchildren <- mapE (\expr => fillHoleExpr expr) children
                                                  pure (MkTLSTypeExpr type cchildren)
  fillHoleType (MkTLSTypeArray mult args) = do cargs <- mapE (\(name, expr) => pure (name, !(fillHoleType expr))) args
                                               pure (MkTLSTypeArray mult cargs)
  fillHoleType (MkTLSTypeBare (MkTLSTypeBare expr)) = pure $ MkTLSTypeBare !(fillHoleType expr)
  fillHoleType (MkTLSTypeBare expr) = pure $ MkTLSTypeBare !(fillHoleType expr)
  fillHoleType (MkTLSTypeBang expr) = pure $ MkTLSTypeBang !(fillHoleType expr)
  fillHoleType (MkTLSTypeHole name xs) = do exprs <- mapE (\expr => fillHoleExpr expr) xs
                                            checkType name exprs False
  fillHoleType x = pure x

fillHoleArgs : TLSArg -> TEff TLSArg
fillHoleArgs x = mapType x fillHoleType

fillTypeHolesFunctions : TEff ()
fillTypeHolesFunctions = do ffuncs <- mapE (\func => fillTypeHolesFunctionHelper func) (functions !(Store :- get))
                            Store :- update (record { functions = ffuncs })
                            pure ()
  where
    fillTypeHolesFunctionHelper : TLSFunction -> TEff TLSFunction
    fillTypeHolesFunctionHelper (MkTLSFunction identifier magic args resultType)
      = do cargs <- mapE (\arg => fillHoleArgs arg) args
           ctype <- fillHoleType resultType
           pure $ MkTLSFunction identifier magic cargs ctype

fillTypeHolesConstructors : TEff ()
fillTypeHolesConstructors = do fconstrs <- mapE (\constr => fillTypeHolesConstructorsHelper constr) (constructors !(Store :- get))
                               Store :- update (record { constructors = fconstrs })
                               pure ()
  where
    fillTypeHolesConstructorsHelper : TLSConstructor -> TEff TLSConstructor
    fillTypeHolesConstructorsHelper (MkTLSConstructor identifier magic args cref type)
      = do cargs <- mapE (\arg => fillHoleArgs arg) args
           pure $ MkTLSConstructor identifier magic cargs cref type

export
fillTypeHoles : TEff ()
fillTypeHoles = do fillTypeHolesFunctions
                   fillTypeHolesConstructors
                   pure ()

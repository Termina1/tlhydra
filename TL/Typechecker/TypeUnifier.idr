module TL.Typechecker.TypeUnifier

import TL.Store.Store
import TL.Types

import Effects
import Effect.State
import Effect.Exception
import Effect.StdIO

%access public export

convertTypeIdentToRef : TLName -> TEff (Maybe TypeRef)
convertTypeIdentToRef name = pure $ storeNameToType name !(Store :- get)

checkTypeEquivalence : TLSTypeExpr -> TLSTypeExpr -> Bool
checkTypeEquivalence a b = a == b

refToVar : VarRef -> TEff TLSArg
refToVar ref = do args <- Args :- get
                  case drop (cast ref) args of
                       [] => raise "Var should be here"
                       (x :: xs) => pure x

unifyParamAndExpr : TLTypeParam -> TLSExpr -> TEff Bool
unifyParamAndExpr TLParamNat (MKTLSExprNat natExpr) = pure True
unifyParamAndExpr TLParamType (MkTLSExprType (MkTLSTypeBare expr)) = unifyParamAndExpr TLParamType (MkTLSExprType expr)
unifyParamAndExpr TLParamType (MkTLSExprType (MkTLSTypeVar ref)) = do var <- refToVar ref
                                                                      pure $ checkTypeEquivalence (argType var) TLTypeType
unifyParamAndExpr TLParamType (MkTLSExprType (MkTLSTypeExpr _ _)) = pure True
unifyParamAndExpr TLParamType (MkTLSExprType (MkTLSTypeHole _ _)) = pure True
unifyParamAndExpr _ _ = pure False

unifyParamsAndExpression : List TLTypeParam -> List TLSExpr -> TEff Bool
unifyParamsAndExpression [] [] = pure True
unifyParamsAndExpression [] (x :: xs) = pure False
unifyParamsAndExpression (x :: xs) [] = pure False
unifyParamsAndExpression (x :: xs) (y :: ys) = if !(unifyParamAndExpr x y)
                                                  then unifyParamsAndExpression xs ys
                                                  else pure False

assertTypeParams : TypeRef -> List TLSExpr -> TEff ()
assertTypeParams x xs = let type = storeGetType x !(Store :- get) in
                        if !(unifyParamsAndExpression (getTypeParams type) xs)
                           then pure ()
                           else raise $ "TypeError: cant unify types and expression, type: " ++ (show type) ++ ", params: " ++ (show xs)

convertCombinatorNameToType : TLName -> TEff (Maybe TypeRef)
convertCombinatorNameToType x = case storeNameToConstructor x !(Store :- get) of
                                     Nothing => pure Nothing
                                     -- this case saves a link to constructor, for bare type
                                     (Just (MkTLSConstructor identifier magic args cref (Right (ref, _)))) => pure $ Just $ Right (ref, cref)
                                     (Just (MkTLSConstructor identifier magic args cref ref)) => pure $ Just ref

mutual
  convertHelper : Bool -> TLName -> List TLSExpr -> TEff TLSTypeExpr
  convertHelper holes name params = case !(convertCombinatorNameToType name) of
                                          Nothing => if holes then pure $ MkTLSTypeHole name params
                                                              else raise $ "Undefined combnator name: " ++ (show name)
                                          Just ref => do type <- checkTypeHelper (Just ref) holes name params
                                                         pure $ MkTLSTypeBare type
  checkType : TLName -> List TLSExpr -> Bool -> TEff TLSTypeExpr
  checkType cname@(MkTLNameNs ns name TLNameTypeLC) params holes = convertHelper holes cname params
  checkType cname@(MkTLName name TLNameTypeLC) params holes = convertHelper holes cname params
  checkType name params holes = checkTypeHelper !(convertTypeIdentToRef name) holes name params

  checkTypeHelper : Maybe TypeRef -> Bool -> TLName -> List TLSExpr -> TEff TLSTypeExpr
  checkTypeHelper ref holes name params = case ref of
                                               Nothing => if holes then pure $ MkTLSTypeHole name params
                                                                   else raise $ "Unknown type name: " ++ (show name)
                                               (Just ref) => do assertTypeParams ref params
                                                                pure $ MkTLSTypeExpr ref params

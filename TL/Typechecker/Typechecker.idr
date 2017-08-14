module TL.Typechecker.Typechecker

import TL.Types
import TL.Parser.Support
import TL.Typechecker.Normalizer

import Effects
import Effect.State
import Effect.Exception
import Effect.StdIO

import TL.Store.Store
import TL.Typechecker.TypeUnifier
import TL.TypeChecker.TypeholeFiller

nameToVar : List TLSArg -> String -> Maybe TLSArg
nameToVar [] x = Nothing
nameToVar (y :: xs) x = if (argId y) == x then Just y else nameToVar xs x

varToRef : TLSArg -> VarRef
varToRef (MkTLSArg id var_num type) = var_num
varToRef (MkTLSArgCond id var_num cond type) = var_num
varToRef (MkTLSArgOpt id var_num type) = var_num

insertVar : TLSArg -> TEff TLSArg
insertVar arg = do Args :- update (\ls => ls ++ [arg])
                   pure arg

generateRef : TTEff VarRef
generateRef = do ref <- VarRefs :- get
                 VarRefs :- update (+ 1)
                 pure ref

insertConstructor : TLSConstructor -> TEff ()
insertConstructor constr = do Store :- update (storeInsertConstructor constr)
                              pure ()

insertFunction : TLSFunction -> TEff ()
insertFunction func = do Store :- update (storeInsertFunction func)
                         pure ()

insertType : TLType -> TEff TypeRef
insertType type = do Store :- update (storeInsertType type)
                     store <- Store :- get
                     pure $ Right $ (cast $ length (types store)) - 1

checkArgType : TLSArg -> List TLSTypeExpr -> TEff ()
checkArgType var xs = let type = argType var in
                          if any (checkTypeEquivalence type) xs
                             then pure ()
                             else raise $ "Var " ++ (argId var) ++ " is of an unexpected type"

compareTypeParams : TypeRef -> List TLTypeParam -> List TLExpressionLang -> TEff ()
compareTypeParams ref params s = let type = storeGetType ref !(Store :- get) in
                                 if (getTypeParams type) == params
                                    then pure ()
                                    else raise $ "Wrong parameters for type: " ++ (show ref) ++ " and params " ++ (show s)

checkTypeParamType : TLSTypeExpr -> TEff TLTypeParam
checkTypeParamType (MkTLSTypeExpr (Left TLTType) []) = pure TLParamType
checkTypeParamType (MkTLSTypeExpr (Left TLNat) []) = pure TLParamNat
checkTypeParamType x = raise $ "Not permitted type to depend: " ++ (show x)

checkTypeParam : TLExpressionLang -> TEff (List TLTypeParam)
checkTypeParam param@(TLEIdent (MkTLName name type)) = case nameToVar !(Args :- get) name of
                                                            Nothing => raise $ "Var not existed: " ++ (show param)
                                                            (Just arg) => do cparam <- checkTypeParamType $ argType arg
                                                                             pure [cparam]
checkTypeParam (TLEExpression params) = do ls <- mapE (\expr => checkTypeParam expr) params
                                           pure (join ls)

checkTypeParam expr = raise $ "Not a type param: " ++ (show expr)

checkResultType : TLExpressionLang -> TEff TypeRef
checkResultType (TLEIdent cname) with (nameType cname)
  checkResultType (TLEIdent cname) | TLNameTypeLC = raise $ "Type name should start from big letter: " ++ (show cname)
  checkResultType (TLEIdent cname) | TLNameTypeUC = case !(convertTypeIdentToRef cname) of
                                                         Nothing => insertType $ MkTLType (show cname) []
                                                         (Just typeRef) => pure typeRef
checkResultType (TLEExpression ((TLEIdent cname) :: params)) = do cparams <- mapE (\expr => checkTypeParam expr) params
                                                                  let tparams = join cparams
                                                                  case !(convertTypeIdentToRef cname) of
                                                                       Nothing => insertType $ MkTLType (show cname) tparams
                                                                       (Just ref) => do compareTypeParams ref tparams params
                                                                                        pure ref
checkResultType expr = raise $ "Not a type: " ++ (show expr)

assertVarNotExist : TLVarName -> TLExpressionLang -> TEff ()
assertVarNotExist MkTLVarOpt type = pure ()
assertVarNotExist name type = case nameToVar !(Args :- get) (show name) of
                                   Nothing => pure ()
                                   (Just x) => raise $ "Duplicate var name: " ++ (show name) ++ " type " ++ (show type)

checkCond : TLECond -> TEff Conditional
checkCond (name, bit) = case nameToVar !(Args :- get) name of
                             Nothing => raise "Can't depend on undeclared var"
                             (Just arg) => pure $ ((varToRef arg), (cast bit))

assertCombinatorName : TLCName -> TLSection -> TEff ()
assertCombinatorName x section with (section)
  assertCombinatorName x section | Types = case storeNameToConstructor (getName x) !(Store :- get) of
                                                Nothing => pure ()
                                                Just comb => raise $ "Duplicate name for constructour: " ++ (show x)
  assertCombinatorName x section | Functions = case storeNameToFunction (getName x) !(Store :- get) of
                                                    Nothing => pure ()
                                                    Just comb => raise $ "Dulpicate name for function: " ++ (show x)

assertSection : TLSection -> TEff ()
assertSection x = if !(Section :- get) == x
                     then pure ()
                     else raise $ "Now is not a section " ++ (show x)


checkVarWithType : TLName -> TLSTypeExpr -> TEff (Maybe VarRef)
checkVarWithType name expr = case nameToVar !(Args :- get) (show name) of
                                  Nothing => pure Nothing
                                  (Just (MkTLSArgCond id var_num cond type)) => pure Nothing
                                  (Just var) => if checkTypeEquivalence (argType var) expr
                                                   then pure $ Just $ varToRef var
                                                   else pure Nothing


checkIdent : TLName -> TEff TLSTypeExpr
checkIdent cname@(MkTLName name type) = case nameToVar !(Args :- get) (show cname) of
                                             Nothing => checkType cname [] True
                                             (Just arg) => do checkArgType arg [TLNatType, TLTypeType]
                                                              pure $ MkTLSTypeVar (argRef arg)
checkIdent cname@(MkTLNameNs ns name type) = checkType cname [] True


-- TODO: process constructor names as bare types
checkTypeIdent : TLExpressionLang -> TLExpressionLang -> TEff TLName
checkTypeIdent (TLEIdent x) c = pure x
checkTypeIdent x c = raise $ "Not a type ident: " ++ (show c)

checkNatExpression : TLExpressionLang -> TEff (Maybe TLSNat)
checkNatExpression (TLENat k) = pure $ Just $ MkTLSNat k
checkNatExpression (TLEIdent x) = case !(checkVarWithType x TLNatType) of
                                       Nothing => pure Nothing
                                       (Just varRef) => pure $ Just $ MkTLSNatVar varRef
checkNatExpression (TLEExpression (x :: [])) = checkNatExpression x
checkNatExpression _ = pure Nothing

catch : TEff a -> TEff (Either String a)
catch eff = pure $ runInit [Store := !(Store :- get), Args := !(Args :- get), Section := !(Section :- get), default] eff

mutual
  checkExpression : TLExpressionLang -> TEff TLSExpr
  checkExpression expr = case !(checkNatExpression expr) of
                              Nothing => do type <- checkTypeExpression expr
                                            pure $ MkTLSExprType type
                              Just nat => pure $ MKTLSExprNat nat

  checkExprArgs : TLEArg -> TEff TLSEArg
  checkExprArgs (MkTLEArg name type) = do expr <- checkTypeExpression type
                                          pure $ ((show name), expr)
  checkExprArgs (MkTLEOptArg name type) = raise "No optional vars in expression args"
  checkExprArgs (MkTLEArgCond name cond type) = raise "No conditional vars inside expression args"

  checkTypeExpression : TLExpressionLang -> TEff TLSTypeExpr
  checkTypeExpression (TLENat k) = raise "Nat is not an expression!"
  checkTypeExpression (TLEIdent cname@(MkTLName name TLNameTypeLC)) = case name of
                                                                          "int" => pure TLIntTypeBare
                                                                          "long" => pure TLLongTypeBare
                                                                          "string" => pure TLStringTypeBare
                                                                          "double" => pure TLDoubleTypeBare
                                                                          _ => do ident <- checkIdent cname
                                                                                  case ident of
                                                                                    (MkTLSTypeVar _) => pure ident
                                                                                    _ => pure $ MkTLSTypeBare ident

  checkTypeExpression (TLEIdent cname@(MkTLName name TLNameTypeUC)) = case name of
                                                                          "Int" => pure TLIntType
                                                                          "Long" => pure TLLongType
                                                                          "String" => pure TLStringType
                                                                          "Double" => pure TLDoubleType
                                                                          "Type" => pure TLTypeType
                                                                          _ => checkIdent cname

  checkTypeExpression (TLEIdent name@(MkTLNameNs ns _ type)) = checkIdent name

  checkTypeExpression TLEHash = pure TLNatType
  checkTypeExpression TLEEmpty = raise "No Empty Expressions allowed!"
  checkTypeExpression (TLEOperator TLBareOperator y) = checkTypeExpression y >>= \expr => pure $ MkTLSTypeBare expr
  checkTypeExpression (TLEOperator TLBangOperator y) = do expr <- checkTypeExpression y
                                                          pure $ MkTLSTypeBang expr
  checkTypeExpression (TLEOperator TLPlus _) = raise "Arithmetic operations should be already reduced!"
  checkTypeExpression (TLEExpression ((TLEOperator TLBareOperator x) :: xs)) = do expr <- checkTypeExpression (TLEExpression (x :: xs))
                                                                                  pure $ MkTLSTypeBare expr
  checkTypeExpression c@(TLEExpression (x :: xs)) = do ident <- checkTypeIdent x c
                                                       args <- mapE (\exp => checkExpression exp) xs
                                                       checkType ident args True
  checkTypeExpression (TLEMultiArg x xs) = do args <- mapE (\x => checkExprArgs x) xs
                                              case !(checkNatExpression x) of
                                                   Nothing => do sargs <- Args :- get
                                                                 case nonEmpty sargs of
                                                                      Yes _ => (do let var = last sargs
                                                                                   checkArgType var [TLNatType]
                                                                                   let nat = MkTLSNatVar (varToRef var)
                                                                                   pure $ MkTLSTypeArray nat args)
                                                                      No _ => raise "Need prev Nat arg for multi expression"

                                                   Just nat =>  pure $ MkTLSTypeArray nat args

checkTypeExpressionAndNormalize : TLExpressionLang -> TEff TLSTypeExpr
checkTypeExpressionAndNormalize expr = checkTypeExpression (expressionReduce expr)

checkArg : TLEArg -> TTEff TLSArg
checkArg (MkTLEArg name type) = do assertVarNotExist name type
                                   expr <- checkTypeExpressionAndNormalize type
                                   ref <- generateRef
                                   insertVar $ (MkTLSArg (show name) ref expr)

checkArg (MkTLEOptArg name type) = do assertVarNotExist name type
                                      expr <- checkTypeExpressionAndNormalize type
                                      if ((checkTypeEquivalence expr TLNatType) || (checkTypeEquivalence expr TLTypeType))
                                         then (do ref <- generateRef
                                                  insertVar $ (MkTLSArgOpt (show name) ref expr))
                                         else raise "Optional vars should of type # or Type"

checkArg (MkTLEArgCond name cond type) = do assertVarNotExist name type
                                            cd <- checkCond cond
                                            expr <- checkTypeExpressionAndNormalize type
                                            ref <- generateRef
                                            insertVar $ (MkTLSArgCond (show name) ref cd expr)

checkCombinator : TLCombinator -> TTEff ()
checkCombinator comb = do section <- Section :- get
                          assertCombinatorName (identifier comb) section
                          Args :- put []
                          VarRefs :- put 0
                          cargs <- mapE (\arg => checkArg arg) (args comb)
                          (case section of
                                Types => do typeRef <- checkResultType (expressionReduce (resultType comb))
                                            insertConstructor $ MkTLSConstructor (show $ getName (identifier comb)) 0 cargs typeRef
                                Functions => do type <- checkTypeExpression (expressionReduce (resultType comb))
                                                insertFunction $ MkTLSFunction (show $ getName (identifier comb)) 0 cargs type)

checkDeclaration : TLDeclaration -> TTEff ()
checkDeclaration (Combinator x) = checkCombinator x
checkDeclaration (BuiltInCombinator x) = pure ()
checkDeclaration (FinalDecl x y) = pure ()

checkDeclarationBlock : TLDeclarationBlock -> TTEff ()
checkDeclarationBlock (TypeDeclarationBlock xs) = do Section :- put Types
                                                     mapE (\decl => checkDeclaration decl) xs
                                                     pure ()
checkDeclarationBlock (FunctionDeclarationBlock xs) = do Section :- put Functions
                                                         mapE (\decl => checkDeclaration decl) xs
                                                         pure ()

checkProgram : TLProgram -> TTEff TLStore
checkProgram (MkTLProgram xs) = do mapE (\block => checkDeclarationBlock block) xs
                                   fillTypeHoles
                                   Store :- get

export
runTypechecker : TLProgram -> Either String TLStore
runTypechecker program = runInit [
    Store := emptyStore,
    Args := [],
    Section := Types,
    default,
    VarRefs := 0
  ] (checkProgram program)

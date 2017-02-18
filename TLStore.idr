module TLStore

import Effects
import Effect.State
import Effect.Exception
import TLMagic

import Data.SortedMap
import Data.Vect

import TLParserTypes
import TLStoreTypes

natType : TLSTypeExpr
natType = TLSTypeExprExpr "#" []

mutual
  evaluateTerm : TLTerm -> Maybe Nat
  evaluateTerm (TermExpr ys) = evaluateExps ys
  evaluateTerm (TermTypeIdent z) = Nothing
  evaluateTerm (TermVarIdent z) = Nothing
  evaluateTerm (TermNatConst k) = Just k
  evaluateTerm (TermTerm z) = Nothing
  evaluateTerm (TermTypeWithExpr z ys) = Nothing

  evaluateExp : TLSubExpr -> Maybe Nat
  evaluateExp (SubExprTerm x y) = do res1 <- evaluateTerm x
                                     res2 <- evaluateExp y
                                     Just (res1 + res2)
  evaluateExp SubExprEmpty = Just 0
  evaluateExp (SubExprSum k x) = do resSub <- evaluateExp x
                                    Just (k + resSub)

  evaluateExp (SubExprSeq x y) = do res1 <- evaluateExp x
                                    res2 <- evaluateExp y
                                    Just (res1 + res2)

  evaluateExps : List TLSubExpr -> Maybe Nat
  evaluateExps xs = foldl (liftA2 (+)) (Just 0) (map evaluateExp xs)

prepareBuiltinForMagic : String -> String -> String
prepareBuiltinForMagic name type = name ++ " ? = " ++ type

createBuiltin : TLIdentLcFull -> TLIdentLcNs -> TLSType
createBuiltin constName typeName = let tname = show typeName in
                                   let cname = show constName in
                                   let magic = calculateMagic (prepareBuiltinForMagic cname tname) in
                                   let const = MkTLCombinator cname magic Nil Nil in
                                   let typeExpr = TLSTypeExprExpr tname Nil in
                                   MkTLSType tname typeExpr (insert tname const empty)

insertType : String -> TLSType -> TLStore -> TLStore
insertType name type store = record { types = (insert name type (types store)) } store

parseBuiltin : TLBuiltIn -> Eff () [(STATE TLStore), EXCEPTION String]
parseBuiltin (MkTLBuiltIn (Opt param) type) = do state <- get
                                                 (case lookup (show type) (types state) of
                                                       Nothing => do update (insertType (show type) (createBuiltin param type))
                                                                     pure ()
                                                       (Just x) => raise ("Duplicate builtin declaration: " ++ (show type)))

parseBuiltin (MkTLBuiltIn Ignore type) = raise "Can't use _ as a builtin combinator name"

selectVarById : String -> List TLSArg -> Maybe TLSArg
selectVarById x xs = find (\el => (case TLSArg.id el of
                                        Nothing => False
                                        (Just x') => x' == x )) xs

assertVarType : TLSTypeExpr -> List TLSArg -> String -> Eff () [EXCEPTION String]
assertVarType typeExpr args varId with (selectVarById varId args)
  assertVarType typeExpr args varId | Nothing = raise $ "Not found var " ++ varId ++ " previously declared"
  assertVarType typeExpr args varId | (Just (MkTLSArg x condition type)) = 
    case type == typeExpr of
      False => raise $ "var " ++ varId ++ "should be of type Nat to be used in conditons"
      True => pure ()

parseConditional : Maybe TLConditionalDef -> List TLSArg -> Eff (Maybe TLCondition) [EXCEPTION String]
parseConditional cond args = case cond of
                                  Nothing => pure Nothing
                                  (Just (MkTLConditionalDef ident nat)) => do assertVarType natType args ident
                                                                              (case nat of
                                                                                Nothing => pure $ Just $ TLConditionVar ident
                                                                                (Just x) => pure $ Just $ TLConditionVarBit ident x)

parseSimpleTermToType : TLTerm -> Maybe TLSTypeExpr
parseSimpleTermToType (TermExpr xs) = ?parseSimpleTermToType_rhs_1
parseSimpleTermToType (TermTypeIdent (TypeIdentBoxed x)) = Just $ TLSTypeExprBoxed (TLSTypeExprExpr (show x) [])
parseSimpleTermToType (TermTypeIdent (TypeIdentLc x)) = Just $ TLSTypeExprExpr (show x) []
parseSimpleTermToType (TermTypeIdent TypeIdentHash) = Just natType
parseSimpleTermToType (TermVarIdent x) = pure $ TLSTypeExprVar x
parseSimpleTermToType (TermNatConst k) = Nothing
parseSimpleTermToType (TermTerm x) = map TLSTypeExprUnboxed (parseSimpleTermToType x)
parseSimpleTermToType (TermTypeWithExpr x xs) = ?parseSimpleTermToType_rhs_6

parseTermToType : Bool -> TLTerm -> List TLSArg -> Eff TLSTypeExpr [(STATE TLStore), EXCEPTION String]
parseTermToType True _ _ = raise "Types with '!' are not supported"
parseTermToType False term args = ?hole--parseSimpleTermToType term

parseArg : TLArg -> List TLSArg -> Eff TLSArg [EXCEPTION String]
parseArg (ArgSimple x cond z w) acc = do tlcond <- parseConditional cond acc
                                         ?hole
parseArg (ArgVector x y xs) acc = ?parseArgs_rhs_2
parseArg (ArgBraces xs x y) acc = ?parseArgs_rhs_3
parseArg (ArgShort x y) acc = ?parseArgs_rhs_4

parseArgs : List TLArg -> Eff (List TLSArg) [EXCEPTION String]
parseArgs args = parseArgsHelper args []
  where
    parseArgsHelper : List TLArg -> List TLSArg -> Eff (List TLSArg) [EXCEPTION String]
    parseArgsHelper [] done = pure done
    parseArgsHelper (x :: xs) done = do tlarg <- parseArg x done
                                        parseArgsHelper xs (tlarg :: done)



-- TODO: Result type can be type var only for function section
assertResultType : TLSection -> Eff () [(STATE TLStore), EXCEPTION String]
assertResultType section = pure ()

parseCombinator : TLCombinator -> TLSection -> Eff () [(STATE TLStore), EXCEPTION String]
parseCombinator (MkTLCombinator identifier optArgs args resultType) section =
  do assertResultType section
     tlArgs <- parseArgs args
     ?hole

parseType : TLDeclaration -> Eff () [(STATE TLStore), EXCEPTION String]
parseType (Combinator x) = ?hole1
parseType (BuiltInCombinator builtin) = parseBuiltin builtin
parseType (FinalDecl x y) = ?hole2

parseTypes : List TLDeclaration -> Eff () [(STATE TLStore), EXCEPTION String]
parseTypes [] = pure ()
parseTypes (decl :: decls) = do parseType decl
                                parseTypes decls


validateAstAndConvertToStore' : TLProgram -> Eff TLStore [(STATE TLStore), EXCEPTION String]
validateAstAndConvertToStore' (MkTLProgram []) = ?validateAstAndConvertToStore'_rhs
validateAstAndConvertToStore' (MkTLProgram (block :: blocks)) = case block of
                                                                     (TypeDeclarationBlock xs) => do parseTypes xs
                                                                                                     t <- get
                                                                                                     pure t
                                                                     (FunctionDeclarationBlock xs) => ?validateAstAndConvertToStore'_rhs_2

validateAstAndConvertToStore : TLProgram -> Either String TLStore
validateAstAndConvertToStore x = runInit [(MkTLStore empty empty empty), default] (validateAstAndConvertToStore' x)

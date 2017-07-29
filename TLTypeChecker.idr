module TLStore

import Effects
import Effect.State
import Effect.Exception
import TLMagic

import Data.SortedMap
import Data.Vect

import TLParserTypes
import TLStoreTypes

%access public export

natType : TLSTypeExpr
natType = TLSTypeExprExpr "#" []

typeType : TLSTypeExpr
typeType = TLSTypeExprExpr "Type" []

data Args : Type where
data Store : Type where

StoreEffect : Type -> Type
StoreEffect ret = Effects.SimpleEff.Eff ret [STATE TLStore, EXCEPTION String]

ArgEffect : Type -> Type
ArgEffect ret = Effects.SimpleEff.Eff ret [Args ::: (STATE (List TLSArg)), EXCEPTION String]

ArgFullEffect : Type -> Type
ArgFullEffect ret = Effects.SimpleEff.Eff ret [Args ::: (STATE (List TLSArg)), Store ::: (STATE TLStore), EXCEPTION String]

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
                                   let typeExpr = TLSTypeExprExpr tname Nil in
                                   let const = MkTLSCombinator cname magic Nil Nil typeExpr in
                                   MkTLSType tname (insert tname const empty)

insertType : String -> TLSType -> TLStore -> TLStore
insertType name type store = record { types = (insert name type (types store)) } store

parseBuiltin : TLBuiltIn -> Eff () [(STATE TLStore), EXCEPTION String]
parseBuiltin (MkTLBuiltIn (Opt param) type) = do state <- get
                                                 (case lookup (show type) (types state) of
                                                       Nothing => do update (insertType (show type) (createBuiltin param type))
                                                                     pure ()
                                                       (Just x) => raise ("Duplicate builtin declaration: " ++ (show type)))

parseBuiltin (MkTLBuiltIn Ignore type) = raise "Can't use _ as a builtin combinator name"

selectVarById : String -> Eff (Maybe TLSArg) [Args ::: (STATE (List TLSArg))]
selectVarById x = do xs <- Args :- get
                     pure $ find (\el => (case TLSArg.id el of
                                               Nothing => False
                                               (Just x') => x' == x)) xs

assertVarTypes : List TLSTypeExpr -> String -> ArgEffect ()
assertVarTypes typeExprs varId =
  do Just (MkTLSArg id condition type) <- selectVarById varId
       | Nothing => raise ("Not found var " ++ varId ++ " previously declared")
     assertVarTypesHelper typeExprs type
  where
    assertVarTypesHelper : List TLSTypeExpr -> TLSTypeExpr -> ArgEffect ()
    assertVarTypesHelper [] type = raise ("var " ++ varId ++ " should be of type Nat to be used in conditons")
    assertVarTypesHelper (x :: types) type =
      (case type == x of
            False => assertVarTypesHelper types type
            True => pure ())

assertVarType : TLSTypeExpr -> String -> ArgEffect ()
assertVarType type varId = assertVarTypes [type] varId

parseConditional : Maybe TLConditionalDef -> List TLSArg -> ArgEffect (Maybe TLCondition)
parseConditional cond args = case cond of
                                  Nothing => pure Nothing
                                  (Just (MkTLConditionalDef ident nat)) => do assertVarType natType ident
                                                                              (case nat of
                                                                                Nothing => pure $ Just $ TLConditionVar ident
                                                                                (Just x) => pure $ Just $ TLConditionVarBit ident x)

constructTypeExpr : List TLSExpr -> String -> ArgFullEffect TLSTypeExpr
constructTypeExpr children name = pure $ TLSTypeExprExpr name children

parseTypeIdentToType : TLTypeIdent -> (String -> ArgFullEffect TLSTypeExpr) -> ArgFullEffect TLSTypeExpr
parseTypeIdentToType (TypeIdentBoxed x) fn = pure $ TLSTypeExprBoxed !(fn (show x))
parseTypeIdentToType (TypeIdentLc x) fn = fn (show x)
parseTypeIdentToType TypeIdentHash fn = pure natType -- TODO: think what errors this may cause

chooseVar : String -> ArgFullEffect (Maybe TLSArg)
chooseVar x = do Just var <- selectVarById x
                   | Nothing => pure Nothing
                 assertVarTypes [typeType, natType] x
                 pure (Just var)


chooseConstructor : String -> ArgFullEffect (Maybe TLSCombinator)
chooseConstructor x = pure Nothing -- TODO: lookup type or constructor

chooseVarOrConstructor : String -> ArgFullEffect TLSTypeExpr
chooseVarOrConstructor x = do Just var <- chooseVar x
                                | Nothing => do Just constr <- chooseConstructor x
                                                  | Nothing => raise ((show x) ++ " is neither var, nor constructor")
                                                pure $ TLSTypeExprExpr x []
                              pure $ TLSTypeExprVar x



mutual
  pareSubExprToTypeIdent : TLSubExpr -> Eff TLTypeIdent [EXCEPTION String]
  pareSubExprToTypeIdent (SubExprTerm term SubExprEmpty) with (term)
    pareSubExprToTypeIdent (SubExprTerm term SubExprEmpty) | (TermTypeIdent x) = pure x
    pareSubExprToTypeIdent (SubExprTerm term SubExprEmpty) | (TermTerm x) = pareSubExprToTypeIdent (SubExprTerm x SubExprEmpty)
    pareSubExprToTypeIdent (SubExprTerm term SubExprEmpty) | x = raise $ (show x) ++ " is not a type identifier"
  pareSubExprToTypeIdent x = raise $ (show x) ++ " is not a type identifier"

  parseSubExprToType : TLSubExpr -> ArgFullEffect TLSExpr
  parseSubExprToType (SubExprTerm x SubExprEmpty) = parseTermToTypeSecond x

  parseSubExprToType (SubExprSum k x) = case evaluateExp x of
                                             Nothing => raise $ (show x) ++ " is not a nat expression"
                                             (Just x) => pure $ TLExpNat (k + x)
  parseSubExprToType x = raise $ (show x) ++ ": something went wrong or empty subexression"

  parseTypeChildern : TLTypeIdent -> List TLSubExpr -> ArgFullEffect TLSTypeExpr
  parseTypeChildern ident xs = do children <- mapE (\sub => parseSubExprToType sub) xs
                                  -- TODO: assert that types of children match some constructors
                                  parseTypeIdentToType ident (constructTypeExpr children)

  parseSimpleTermToType : TLTerm -> ArgFullEffect TLSTypeExpr
  parseSimpleTermToType (TermExpr xs) with (xs)
    parseSimpleTermToType (TermExpr xs) | [] = raise "Empty expression"
    parseSimpleTermToType (TermExpr xs) | (x :: ys) = do ident <- pareSubExprToTypeIdent x
                                                         parseTypeChildern ident ys

  parseSimpleTermToType (TermTypeIdent typeIdent) = parseTypeIdentToType typeIdent (constructTypeExpr [])
  parseSimpleTermToType (TermVarIdent x) = do assertVarType typeType x
                                              pure $ TLSTypeExprVar x
  parseSimpleTermToType (TermNatConst k) = raise "Type cannot be a nat const"
  parseSimpleTermToType (TermTerm term) = pure $ TLSTypeExprUnboxed !(parseSimpleTermToType term)
  parseSimpleTermToType (TermTypeWithExpr x xs) = raise "Not implemented type with expr" -- TODO: implement

  parseTermToTypeSecond : TLTerm -> ArgFullEffect TLSExpr
  parseTermToTypeSecond (TermTypeIdent typeIdent) = do type <- parseTypeIdentToType typeIdent chooseVarOrConstructor
                                                       pure $ TLExpType type

  parseTermToTypeSecond (TermVarIdent x) = do assertVarTypes [typeType, natType] x
                                              pure $ TLExpType $ TLSTypeExprVar x
  parseTermToTypeSecond (TermNatConst k) = pure $ TLExpNat k
  parseTermToTypeSecond term = do type <- parseSimpleTermToType term
                                  pure $ TLExpType type

parseTermToType : Bool -> TLTerm -> ArgFullEffect TLSTypeExpr
parseTermToType True _ = raise "Types with '!' are not supported"
parseTermToType False term = parseSimpleTermToType term

tloptToMaybe : TLOpt a -> Maybe a
tloptToMaybe opt = case opt of
                        (Opt param) => Just param
                        Ignore => Nothing

parseArg : TLArg -> ArgFullEffect TLSArg
parseArg (ArgSimple x cond z term) = do tlcond <- parseConditional cond !(Args :- get)
                                        type <- parseTermToType z term
                                        pure $ MkTLSArg (tloptToMaybe x) tlcond type

parseArg (ArgVector x y xs) = raise "Not implemented vector args"
parseArg (ArgBraces xs x y) = raise "Not implemented arg braces"
parseArg (ArgShort x y) = raise "Not implemented short args"

parseArgs : List TLArg -> List TLSArg -> StoreEffect (List TLSArg)
parseArgs args prevArgs = case parseArgsHelper args prevArgs !get of
                               (Left l) => raise l
                               (Right r) => pure r
  where
    parseArgsEffectHelper : List TLArg -> ArgFullEffect (List TLSArg)
    parseArgsEffectHelper [] = Args :- get
    parseArgsEffectHelper (x :: xs) = do arg <- parseArg x
                                         Args :- update (\store => arg :: store)
                                         parseArgsEffectHelper xs

    parseArgsHelper : List TLArg -> List TLSArg -> TLStore -> Either String (List TLSArg)
    parseArgsHelper xs prev store = runInit [Args := prev, Store := store, default] (parseArgsEffectHelper xs)

-- TODO: Result type can be type var only for function section
assertResultType : TLSection -> StoreEffect ()
assertResultType x = pure ()

-- TODO: assert that we didnt parse combnator with the same name
assertDuplicate : String -> StoreEffect ()
assertDuplicate x = pure ()


parseResultType : TLResultType -> ArgFullEffect TLSTypeExpr
parseResultType (ResultType ident xs) = parseSimpleTermToType (TermTypeWithExpr (TypeIdentBoxed ident) [xs])
parseResultType (ResultTypeParam ident xs) = parseSimpleTermToType (TermTypeWithExpr (TypeIdentBoxed ident) [xs])

parseResultTypeWithEffects : TLResultType -> List TLSArg -> List TLSArg -> StoreEffect TLSTypeExpr
parseResultTypeWithEffects rtype optargs args = case parseResultHelper rtype !get (args ++ optargs) of
                                                     (Left l) => raise l
                                                     (Right r) => pure r
  where
    parseResultHelper : TLResultType -> TLStore -> List TLSArg -> Either String TLSTypeExpr
    parseResultHelper hrtype hstore hargs = runInit [Args := hargs, Store := hstore, default] (parseResultType hrtype)


getOrCreateType : String -> StoreEffect TLSType
getOrCreateType k = do store <- get
                       (case lookup k (types store) of
                             Nothing => do update (record { types = insert k (MkTLSType k empty) (types store) })
                                           pure (MkTLSType k empty)
                             Just type => pure type)

resultTypeKey : TLResultType -> String
resultTypeKey (ResultType x xs) = show x
resultTypeKey (ResultTypeParam x xs) = show x

getCombinatorNameAndMagic : TLOpt TLIdentLcFull -> TLCombinator -> StoreEffect (String, Integer)
getCombinatorNameAndMagic (Opt (IdentLcFull name)) comb = pure (show name, calculateMagic (show comb))
getCombinatorNameAndMagic (Opt (IdentLcFullMagic name y)) comb = case ensureMagic comb of
                                                                   (Left error) => raise error
                                                                   (Right magic) => pure (show name, magic)
getCombinatorNameAndMagic Ignore comb = pure ("_", calculateMagic (show comb))

createCombinator : TLCombinator -> TLOpt TLIdentLcFull -> List TLSArg -> List TLSArg -> TLSTypeExpr -> TLSType -> StoreEffect TLSType
createCombinator comb ident optArgs args rtype tltype =
  do (name, magic) <- getCombinatorNameAndMagic ident comb
     let combinator = MkTLSCombinator name magic optArgs args rtype
     pure $ record { constructors = insert name combinator (constructors tltype) } tltype

parseCombinator : TLCombinator -> TLSection -> Eff () [(STATE TLStore), EXCEPTION String]
parseCombinator comb@(MkTLCombinator identifier optArgs args resultType) section =
  let tkey = resultTypeKey resultType in
      (do assertResultType section
          assertDuplicate (show identifier)
          optArgs <- parseArgs optArgs []
          tlArgs <- parseArgs args optArgs
          tlExpr <- parseResultTypeWithEffects resultType optArgs tlArgs
          tltype <- getOrCreateType tkey
          store <- get
          tlscomb <- createCombinator comb identifier optArgs tlArgs tlExpr tltype
          update (record { types = insert tkey tlscomb (types store)}))

parseType : TLDeclaration -> Eff () [(STATE TLStore), EXCEPTION String]
parseType (Combinator x) = parseCombinator x TLSectionTypes
parseType (BuiltInCombinator builtin) = parseBuiltin builtin
parseType (FinalDecl x y) = raise "Not implemented!"

parseTypes : List TLDeclaration -> Eff () [(STATE TLStore), EXCEPTION String]
parseTypes [] = pure ()
parseTypes (decl :: decls) = do parseType decl
                                parseTypes decls


validateAstAndConvertToStore' : TLProgram -> Eff TLStore [(STATE TLStore), EXCEPTION String]
validateAstAndConvertToStore' (MkTLProgram []) = get
validateAstAndConvertToStore' (MkTLProgram (block :: blocks)) = case block of
                                                                     (TypeDeclarationBlock xs) => do parseTypes xs
                                                                                                     t <- get
                                                                                                     pure t
                                                                     (FunctionDeclarationBlock xs) => raise "Not implemented"

validateAstAndConvertToStore : TLProgram -> Either String TLStore
validateAstAndConvertToStore x = runInit [(MkTLStore empty empty empty), default] (validateAstAndConvertToStore' x)

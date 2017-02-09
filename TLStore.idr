module TLStore

import Data.SortedMap
import Data.Vect

import TLParserTypes
import TLMagic
import TLStoreTypes

NAT_ERROR : String
NAT_ERROR = "only var name or nat expressions are allowed"

joinS : List String -> String
joinS xs = foldl (\acc, el => acc ++ " " ++ el) "" xs

maybeToString : Maybe String -> String
maybeToString Nothing = ""
maybeToString (Just x) = x ++ "."

prepareIdentNs : TLIdentLcNs -> String
prepareIdentNs (MkTLIdentLcNs ns ident) = (maybeToString ns) ++ ident

prepareIdentifier : TLOpt TLIdentLcFull -> String
prepareIdentifier (Opt (IdentLcFull ident)) = prepareIdentNs ident
prepareIdentifier (Opt (IdentLcFullMagic ident magic)) = prepareIdentNs ident
prepareIdentifier Ignore = "_"

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
  evaluateExps xs = foldl (\acc, sub => acc >>= \a => evaluateExp sub >>= \b => pure $ a + b) (Just 0) xs

termToNatExpr : TLTerm -> Either String TLSNatExpr
termToNatExpr (TermExpr xs) = case evaluateExps xs of
                                   Nothing => Left $ joinS ["Not a nat expression", (show xs), NAT_ERROR]
                                   (Just x) => Right (TLNatExprConst x)
termToNatExpr (TermTypeIdent x) = Left $ joinS ["Invalid type idnetifier,", (show x) , NAT_ERROR]
termToNatExpr (TermVarIdent name) = Right (TLNatExprVar name)
termToNatExpr (TermNatConst k) = Right (TLNatExprConst k)
termToNatExpr (TermTerm x) = Left $ joinS ["Invalid term", (show x), NAT_ERROR]
termToNatExpr (TermTypeWithExpr x xs) = Left $ joinS ["Invalid type", (show x), NAT_ERROR]

termToType : TLTerm -> Bool -> Either String TLSType
-- termToType (TermExpr xs) excl = ?termToType_rhs_1
-- termToType (TermTypeIdent x) excl = ?termToType_rhs_2
-- termToType (TermVarIdent x) excl = ?termToType_rhs_3
-- termToType (TermNatConst k) excl = ?termToType_rhs_4
-- termToType (TermTerm x) excl = ?termToType_rhs_5
-- termToType (TermTypeWithExpr x xs) excl = ?termToType_rhs_6

mutual
  argTermToType : Maybe TLTerm -> List TLArg -> Either String TLSType
  argTermToType mult args with (mult)
    argTermToType mult args | Nothing = (prepareArgs args) >>= \args => Right $ TLSTypeArray TLSMultiplicityInfer args
    argTermToType mult args | (Just term) = do mult' <- (termToNatExpr term)
                                               args' <- (prepareArgs args)
                                               Right $ TLSTypeArray (TLSMultiplicityExpr mult') args'

  prepareArg : TLArg -> Either String (List TLSArg)
  prepareArg (ArgSimple id y excl type) = (termToType type excl)
                                          >>= \type => Right $ pure $ MkTLSArg (Just $ show id) type
  prepareArg (ArgVector id mult args) = (argTermToType mult args)
                                        >>= \type => Right $ pure $ MkTLSArg (map show id) type
  prepareArg (ArgBraces names excl term) = foldl convertArg (Right []) names
    where
      convertArg : Either String (List TLSArg) -> TLOpt String -> Either String (List TLSArg)
      convertArg acc id = do arr <- acc
                             type <- termToType term excl
                             Right $ [MkTLSArg (Just (show id)) type] ++ arr

  prepareArg (ArgShort excl term) = (termToType term excl)
                                    >>= \type => Right $ pure $ MkTLSArg Nothing type

  prepareArgs : List TLArg -> Either String (List TLSArg)
  prepareArgs args = foldl foldOnArgs (Right []) args
    where
      foldOnArgs : Either String (List TLSArg) -> TLArg -> Either String (List TLSArg)
      foldOnArgs acc arg = do arr <- acc
                              nwargs <- prepareArg arg
                              Right (arr ++ nwargs)

prepareResultType : TLResultType -> TLSType
prepareResultType (ResultType ident xs) = ?prepareResultType_rhs_1
prepareResultType (ResultTypeParam x xs) = ?prepareResultType_rhs_2

prepareTypeCombinator : TLCombinator -> Either String TLSCombinator
prepareTypeCombinator comb = let magic = ensureMagic comb in
                                (case magic of
                                      (Right magic) =>  let identifier = prepareIdentifier (identifier comb) in
                                                        let fixedArgs = prepareArgs (args comb) in
                                                        let optArgs = prepareArgs (optArgs comb) in
                                                        let type = prepareResultType (resultType comb) in
                                                            ?hole
                                                            -- Right (TLStoreTypes.MkTLCombinator identifier magic optArgs fixedArgs type)
                                      (Left err) => Left err)

export
convertAstToStore : TLProgram -> Either String TLStore
convertAstToStore (MkTLProgram blocks) = foldl foldDeclarationBlock (pure (MkTLStore empty empty empty empty)) blocks
  where
    foldDeclarationBlock : Either String TLStore -> TLDeclarationBlock -> Either String TLStore
    foldDeclarationBlock store (TypeDeclarationBlock []) = store
    foldDeclarationBlock store (TypeDeclarationBlock (decl :: decls)) with (decl)
      foldDeclarationBlock store (TypeDeclarationBlock (decl :: decls)) | (Combinator comb)
        = do sdata <- store
             scomb <- prepareTypeCombinator comb
             foldDeclarationBlock (pure (record {
               types = (insert (identifier scomb) scomb (types sdata)),
               magicMapping = (insert (magic scomb) (identifier scomb) (magicMapping sdata))
             } sdata)) (TypeDeclarationBlock decls)

      foldDeclarationBlock store (TypeDeclarationBlock (decl :: decls)) | (BuiltInCombinator bultin) = foldDeclarationBlock store (TypeDeclarationBlock decls)
      foldDeclarationBlock store (TypeDeclarationBlock (decl :: decls)) | (FinalDecl x y) = ?foldDeclarationBlock_rhs_4_rhs_4

    foldDeclarationBlock store (FunctionDeclarationBlock []) = store
    foldDeclarationBlock store (FunctionDeclarationBlock (decl :: decls)) with (decl)
      foldDeclarationBlock store (FunctionDeclarationBlock (decl :: decls)) | (Combinator comb) = ?foldDeclarationBlock_rhs_5_rhs_1
      foldDeclarationBlock store (FunctionDeclarationBlock (decl :: decls)) | (BuiltInCombinator bultin)
        = Left "Built-in combinators are not allowed in 'functions' section"
      foldDeclarationBlock store (FunctionDeclarationBlock (decl :: decls)) | (FinalDecl x y)
        = Left "Final declarations are not allowed in 'functions' section"

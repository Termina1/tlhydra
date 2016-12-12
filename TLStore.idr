module TLStore

import Data.SortedMap
import Data.Vect

import TLParserTypes
import TLMagic
import TLStoreTypes

maybeToString : Maybe String -> String
maybeToString Nothing = ""
maybeToString (Just x) = x ++ "."

prepareArg : TLParserTypes.TLArg -> TLStoreTypes.TLArg
prepareResultType : TLParserTypes.TLResultType -> TLStoreTypes.TLType

prepareIdentifier : TLParserTypes.TLOpt TLParserTypes.TLIdentLcFull -> String
prepareIdentifier (Opt (IdentLcFull (MkTLIdentLcNs ns ident))) = (maybeToString ns) ++ ident
prepareIdentifier (Opt (IdentLcFullMagic (MkTLIdentLcNs ns ident) magic)) = (maybeToString ns) ++ ident
prepareIdentifier Ignore = "_"

prepareTypeCombinator : TLParserTypes.TLCombinator -> Either String TLStoreTypes.TLCombinator
prepareTypeCombinator comb = let magic = ensureMagic comb in
                                (case magic of
                                      (Right magic) =>  let identifier = prepareIdentifier (identifier comb) in
                                                        let fixedArgs = map prepareArg (args comb) in
                                                        let optArgs = map prepareArg (args comb) in
                                                        let type = prepareResultType (resultType comb) in
                                                            Right (TLStoreTypes.MkTLCombinator identifier magic optArgs fixedArgs type)
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

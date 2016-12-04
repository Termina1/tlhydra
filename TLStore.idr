module TLStore

import Data.SortedMap
import Data.Vect

import TLParserTypes

%access public export

data TLArg : Type where

data TLType : Type where

record TLCombinator where
  constructor MkTLCombinator
  identifier : String
  magic : Magic
  optArgs : List TLStore.TLArg
  args : List TLStore.TLArg
  resultType : TLType

data TLFinal : Type where

record TLStore where
  constructor MkTLStore
  magicMapping : SortedMap Magic String
  types : SortedMap String TLStore.TLCombinator
  functions : SortedMap String TLStore.TLCombinator
  finals : SortedMap String TLFinal

%access private

prepareTypeCombinator : TLParserTypes.TLCombinator -> Either String TLStore.TLCombinator
prepareTypeCombinator comb = let magic = ensureMagic comb
                                 in ?hole2

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
             foldDeclarationBlock (pure (record { types = (insert (identifier scomb) scomb (types sdata)) } sdata)) (TypeDeclarationBlock decls)

      foldDeclarationBlock store (TypeDeclarationBlock (decl :: decls)) | (BuiltInCombinator bultin) = ?foldDeclarationBlock_rhs_4_rhs_3
      foldDeclarationBlock store (TypeDeclarationBlock (decl :: decls)) | (FinalDecl x y) = ?foldDeclarationBlock_rhs_4_rhs_4

    foldDeclarationBlock store (FunctionDeclarationBlock []) = store
    foldDeclarationBlock store (FunctionDeclarationBlock (decl :: decls)) with (decl)
      foldDeclarationBlock store (FunctionDeclarationBlock (decl :: decls)) | (Combinator comb) = ?foldDeclarationBlock_rhs_5_rhs_1
      foldDeclarationBlock store (FunctionDeclarationBlock (decl :: decls)) | (BuiltInCombinator bultin)
        = Left "Built-in combinators are not allowed in 'functions' section"
      foldDeclarationBlock store (FunctionDeclarationBlock (decl :: decls)) | (FinalDecl x y)
        = Left "Final declarations are not allowed in 'functions' section"

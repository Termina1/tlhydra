module TL.Serialize.Serializer

import Data.Bits
import Data.Vect

import TL.Types
import TL.Store.Store
import TL.Serialize.Serializable
import Control.ST
import Control.ST.Exception
import Debug.Trace

SerializeContext : Type
SerializeContext = State $ List (VarRef, Either Nat TLSTypeExpr)

SRT : {m : (Type -> Type)} -> {auto var : Var} -> Type -> Type
SRT {m} {var} ret = Control.ST.ST m ret [var ::: SerializeContext]

addToCtx : VarRef -> Either Nat TLSTypeExpr -> (var : Var) -> SRT {m} ()
addToCtx ref val var = do ctx <- read var
                          write var ((ref, val) :: ctx)

getFromCtx : Exception m String => (ctx : Var) -> VarRef -> SRT {m} (Either Nat TLSTypeExpr)
getFromCtx ctx ref = do
  state <- read ctx
  case (find (\(vref, expr) => ref == vref) state) of
    Nothing => throw "Unkonwn type var in expression"
    Just (name, type) => pure type

getNatFromCtx : Exception m String => (ctx : Var) -> VarRef -> SRT {m} Nat
getNatFromCtx ctx ref =
  case !(getFromCtx ctx ref) of
    Left nat => pure nat
    Right type => throw "Type expression where nat was expected"

resolveNatExpression : Exception m String => (ctx : Var) -> TLSNat -> SRT {m} Nat
resolveNatExpression ctx (MkTLSNat nat) = pure nat
resolveNatExpression ctx (MkTLSNatVar ref) = getNatFromCtx ctx ref

bits0 : Stream Bits8
bits0 = repeat $ intToBits' {n = 8} 0

natToBits8 : Integer -> List Bits8
natToBits8 n = tail $ b32ToBytes (intToBits' {n = 32} n)

chartToBit8 : Char -> Bits8
chartToBit8 x = intToBits' {n = 8} $ cast $ ord x

serializeString : String -> List Bits8
serializeString "" = [intToBits' {n = 8} 0]
serializeString x = map chartToBit8 (unpack x)

padBytes : List Bits8 -> List Bits8
padBytes xs with (modNatNZ (length xs) 4 SIsNotZ)
  padBytes xs | Z = xs
  padBytes xs | (S Z) = xs ++ (take 3 bits0)
  padBytes xs | (S (S Z)) = xs ++ (take 2 bits0)
  padBytes xs | (S (S (S k))) = xs ++ (take 1 bits0)

serializeBuiltin : (ty : TLBuiltIn) -> primitive ty -> List Bits8
serializeBuiltin TLInt x = reverse $ b32ToBytes $ intToBits' {n = 32} (cast x)
serializeBuiltin TLNat x = reverse $ b32ToBytes $ intToBits' {n = 32} (cast x)
serializeBuiltin TLLong x = reverse $ b64ToBytes $ intToBits' {n = 64} x
serializeBuiltin TLString x =
  let len = length x in
  if len >= 254
      then let ks = natToBits8 (cast len) in
          padBytes $ (intToBits' {n = 8} 254) :: (ks ++ (serializeString x))
      else padBytes $ (intToBits' {n = 8} (cast len)) :: (serializeString x)
serializeBuiltin TLDouble x = ?serializeBuiltin_rhs_5
serializeBuiltin _ x = []

addTypeOrNatToCtx : Exception m String => (ctx : Var) -> TLSArg -> TLSExpr -> SRT {m} ()
addTypeOrNatToCtx ctx arg (MkTLSExprType type) = addToCtx (argRef arg) (Right type) ctx
addTypeOrNatToCtx ctx arg (MKTLSExprNat (MkTLSNat nat)) = addToCtx (argRef arg) (Left nat) ctx
addTypeOrNatToCtx ctx arg (MKTLSExprNat (MkTLSNatVar ref)) = throw "All type vars should be resolved"

addTypesToCtxt : Exception m String => (ctx : Var) -> List TLTypeParam -> List TLSExpr -> TLSConstructor -> SRT {m} ()
addTypesToCtxt ctx [] [] constr = pure ()
addTypesToCtxt ctx [] (x :: xs) constr = throw $ "Too many arguments for " ++ (show constr)
addTypesToCtxt ctx (x :: xs) [] constr = throw $ "Too few arguments for " ++ (show constr)
addTypesToCtxt ctx (param :: xs) (expr :: ys) constr =
  let paramName = getTypeParamName param in
  let args = args constr in
  let argM = find (\arg => (argId arg) == paramName) args in
  case argM of
       Nothing => throw "Inconsistent store"
       (Just arg) => addTypeOrNatToCtx ctx arg expr

mutual
  serializeSequenceIteration : Exception m String =>
    {auto ctx : Var} -> {auto store : TLStore} -> List (String, TLSTypeExpr) -> List Serializy -> SRT {m} (List Bits8)
  serializeSequenceIteration [] [] = pure []
  serializeSequenceIteration ((name, type) :: vars) (ser :: sers) =
    pure $ !(serializeTypeExpr False type ser) ++ !(serializeSequenceIteration vars sers)
  serializeSequenceIteration _ _ = throw $ "Not enough arguments to serialize sequence"

  serializeSequence : Exception m String =>
    {auto ctx : Var} -> {auto store : TLStore} -> (n : Nat) -> List (String, TLSTypeExpr) -> Vect n (List Serializy) -> SRT {m} (List Bits8)
  serializeSequence Z xs [] = pure []
  serializeSequence (S k) args (seq :: seqs) =
    pure $ !(serializeSequenceIteration args seq) ++ !(serializeSequence k args seqs)

  serializeTypeExpr : Exception m String =>
    {auto ctx : Var} -> {auto store : TLStore} -> Bool -> TLSTypeExpr -> Serializy -> SRT {m} (List Bits8)
  serializeTypeExpr skipMagic (MkTLSTypeExpr (Left ty) []) (SBuiltIn ty1 x) =
    if ty1 == ty
      then pure $ serializeBuiltin ty1 x
      else throw $ "Type mismatch: " ++ (show ty) ++ " vs " ++ (show ty1)
  serializeTypeExpr skipMagic (MkTLSTypeVar varRef) serializy = throw "All type vars should be resolved "
  serializeTypeExpr skipMagic (MkTLSTypeBare expr) serializy =
    serializeTypeExpr True expr serializy
  serializeTypeExpr skipMagic (MkTLSTypeBang expr) serializy =
    throw $ "Bang operator is not supproted: " ++ (show expr)
  serializeTypeExpr skipMagic (MkTLSTypeHole name exprs) serializy =
    throw $ "There is a hole: " ++ (show exprs) ++ ", " ++ (show name)
  serializeTypeExpr {ctx} skipMagic (MkTLSTypeArray cnt args) (SMulti seqs {n}) = do
    iterations <- resolveNatExpression ctx cnt
    case decEq iterations n of
      Yes prf => serializeSequence iterations args (rewrite prf in seqs)
      No contra => throw $ "Sequence " ++ (show seqs) ++ " should be length of " ++ (show iterations)
  serializeTypeExpr {ctx = ctx} skipMagic (MkTLSTypeArray cnt args) ser =
    throw $ "Expeceted sequence insted got " ++ (show ser)
  serializeTypeExpr {store} skipMagic (MkTLSTypeExpr typeRef children) (SExpr name args) =
    let constrM = storeNameToConstructor name store in
    let typeParams = getTypeParams $ storeGetType typeRef store in
    case constrM of
      Nothing => throw $ "Unkown constructor: " ++ (show name)
      (Just constr) =>
        if (resultType constr) == typeRef then
          if skipMagic then do nvar <- new []
                               call $ addTypesToCtxt nvar typeParams children constr
                               result <- call $ serializeTypeConstructor {ctx = nvar} constr args
                               delete nvar
                               pure result
                       else do nvar <- new []
                               call $ addTypesToCtxt nvar typeParams children constr
                               result <- call $ serializeTypeConstructor {ctx = nvar} constr args
                               delete nvar
                               pure $ (serializeBuiltin TLInt (magic constr)) ++ result
          else throw $ "Type mismatch: " ++ (show typeRef) ++ " vs " ++ (show name)
  serializeTypeExpr {store} skipMagic expr sers =
    throw $ "Can't match expression " ++ (show expr) ++ " with arguments " ++ (show sers)

  serializeTypeConstructor : Exception m String =>
    {auto ctx : Var} -> {auto store : TLStore} -> TLSConstructor -> List Serializy -> ST m (List Bits8) [ctx ::: SerializeContext]
  serializeTypeConstructor constr sers = serializeTypeConstructorH sers (args constr)
  where
    serializeTypeConstructorH : Exception m String =>
      {auto ctx : Var} -> List Serializy -> List TLSArg -> SRT {m} (List Bits8)
    serializeTypeConstructorH [] [] = pure []
    serializeTypeConstructorH (ser :: sers) [] = throw $ "Wrong argument count for " ++ (identifier constr)
    serializeTypeConstructorH allsers (arg :: args) = do (bits, sers) <- serializeArg arg allsers
                                                         bitsList <- serializeTypeConstructorH sers args
                                                         pure (bits ++ bitsList)

  replaceTypeVarsArgs : Exception m String => (ctx : Var) -> List (String, TLSTypeExpr) -> SRT {m} (List (String, TLSTypeExpr))
  replaceTypeVarsArgs ctx [] = pure []
  replaceTypeVarsArgs ctx ((name, expr) :: xs) = do
    nwexpr <- replaceTypeVars ctx expr
    pure $ (name, nwexpr) :: !(replaceTypeVarsArgs ctx xs)


  replaceTypeVars : Exception m String => (ctx : Var) -> TLSTypeExpr -> SRT {m} TLSTypeExpr
  replaceTypeVars ctx (MkTLSTypeExpr type children) = do
    nwchildren <- replaceTypeVarsArr ctx children
    pure $ MkTLSTypeExpr type nwchildren
  replaceTypeVars ctx (MkTLSTypeArray (MkTLSNat nat) args) = pure $ (MkTLSTypeArray (MkTLSNat nat) !(replaceTypeVarsArgs ctx args))
  replaceTypeVars ctx (MkTLSTypeArray (MkTLSNatVar ref) args) =
    case !(getFromCtx ctx ref) of
      Left nat => pure $ MkTLSTypeArray (MkTLSNat nat) !(replaceTypeVarsArgs ctx args)
      Right type => throw "Type expression where nat expression was expected"
  replaceTypeVars ctx (MkTLSTypeVar ref) =
    case !(getFromCtx ctx ref) of
      Left nat => throw "Nat expression where type expression was expected"
      Right type => pure type
  replaceTypeVars ctx (MkTLSTypeBare expr) = pure $ MkTLSTypeBare !(replaceTypeVars ctx expr)
  replaceTypeVars ctx (MkTLSTypeBang expr) = throw $ "Bang operator not supported" ++ (show expr)
  replaceTypeVars ctx (MkTLSTypeHole name xs) = throw $ "Unexpected hole in " ++ (show xs)


  replaceTypeVarsArr : Exception m String => (ctx : Var) -> List TLSExpr -> SRT {m} (List TLSExpr)
  replaceTypeVarsArr ctx [] = pure []
  replaceTypeVarsArr ctx ((MkTLSExprType type) :: xs) = pure $ (MkTLSExprType !(replaceTypeVars ctx type)) :: !(replaceTypeVarsArr ctx xs)
  replaceTypeVarsArr ctx ((MKTLSExprNat (MkTLSNatVar ref)) :: xs) =
    case !(getFromCtx ctx ref) of
      Left nat => pure $ (MKTLSExprNat $ MkTLSNat nat) :: !(replaceTypeVarsArr ctx xs)
      Right type => throw "Type expression where nat expression was expected"
  replaceTypeVarsArr ctx (x :: xs) = pure $ x :: !(replaceTypeVarsArr ctx xs)


  serializeArg : Exception m String =>
    {auto ctx : Var} -> {auto store : TLStore} -> TLSArg -> List Serializy -> SRT {m} (List (Bits8), List Serializy)
  serializeArg {ctx} {store = store} (MkTLSArg id var_num TLNatType) (ser@(SBuiltIn TLNat x) :: sers) = do
    addToCtx var_num (Left x) ctx
    pure (!(serializeTypeExpr False TLNatType ser), sers)
  serializeArg {ctx} {store} (MkTLSArg id var_num type) (ser :: sers) = do
    filledExpr <- replaceTypeVars ctx type
    pure (!(serializeTypeExpr False filledExpr ser), sers)
  serializeArg (MkTLSArgOpt id var_num type) ser = pure ([], ser)
  serializeArg {ctx} (MkTLSArgCond id var_num (ref, bit) type) sers = do
    val <- getNatFromCtx ctx ref
    let valBits = MkBits $ natToBits {n = 2} val
    if getBit bit valBits
      then do filledExpr <- replaceTypeVars ctx type
              case sers of
                [] => throw $ "Expecting conditional argument, but none found for " ++ (show id)
                (ser :: sers) => pure (!(serializeTypeExpr False filledExpr ser), sers)
      else pure ([], sers)
  serializeArg _ [] = throw "Empty serialization list"

public export
serializeExpression : TLStore -> Serializy -> Either String (List Bits8)
serializeExpression store ser = run $ serializeExpressionHelper store ser
  where
    serializeExpressionHelper : Exception m String => TLStore -> Serializy -> ST m (List Bits8) []
    serializeExpressionHelper store (SExpr name args) =
      case storeNameToConstructor name store of
        Nothing => throw $ "Uknown constructor " ++ (show name)
        Just constr => do ctx <- new []
                          bytes <- serializeTypeConstructor constr args
                          delete ctx
                          pure $ (serializeBuiltin TLInt (magic constr)) ++ bytes
    serializeExpressionHelper store _ = throw "Top level serialiazable should be a constructor"

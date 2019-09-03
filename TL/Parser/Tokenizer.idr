module TL.Parser.Tokenizer

import Text.Lexer
import Data.String
import Data.Vect
import TL.Types

import TL.Parser.Support

lcLetter : Lexer
lcLetter = pred (\ch => (isAlpha ch) && (isLower ch))

optional : Lexer -> Recognise False
optional r = r <|> empty

ucLetter : Lexer
ucLetter = pred (\ch => (isAlpha ch) && (isUpper ch))

underscore : Lexer
underscore = is '_'

letter : Lexer
letter = lcLetter <|> ucLetter

identChar : Lexer
identChar = letter <|> digit <|> underscore

lcIdent : Lexer
lcIdent = lcLetter <+> many identChar

ucIdent : Lexer
ucIdent = ucLetter <+> many identChar

identNs : Lexer -> Lexer
identNs l = ((some lcIdent <+> is '.') <|> empty) <+> some l

lcIdentNs : Lexer
lcIdentNs = identNs lcIdent

ucIdentNs : Lexer
ucIdentNs = identNs ucIdent

lcIdentFull : Lexer
lcIdentFull = lcIdentNs <+> is '#' <+> (many hexDigit)

comment : Lexer
comment = exact "//" <+> (many (isNot '\n'))

tokenConstMap : Char -> (Lexer, (String -> TLToken))
tokenConstMap c = ((is c), (\s => TLTokenChar (strHead s)))

tokenParseNat : String -> TLToken
tokenParseNat s = case parsePositive s of
                       Nothing => TLTokenFail s
                       (Just x) => TLTokenNat (fromIntegerNat x)

tokenCondDef : String -> TLToken
tokenCondDef s = let mvec = exactLength 2 (fromList (split (== '.') s)) in
                       (case mvec of
                             Nothing => TLTokenFail s
                             (Just x) => (case parsePositive (index 1 x) of
                                               Nothing => TLTokenFail s
                                               (Just num) => TLTokenCond (index 0 x) (fromInteger num)))

tokenSplitChar : Char -> String -> Either String (String, String)
tokenSplitChar chr str = let mvec = exactLength 2 (fromList (split (== chr) str)) in
                             (case mvec of
                                   Nothing => Left str
                                   (Just x) => Right ((index 0 x), (index 1 x)))

tokenIdentFull : String -> TLToken
tokenIdentFull s with (tokenSplitChar '#' s)
  tokenIdentFull s | (Left _) = TLTokenFail s
  tokenIdentFull s | (Right (name, magic)) with (tokenSplitChar '.' name)
    tokenIdentFull s | (Right (name, magic)) | (Left _)
      = TLTokenIdentFull (MkTLName name TLNameTypeLC) magic
    tokenIdentFull s | (Right (name, magic)) | (Right (ns, cname))
      = TLTokenIdentFull (MkTLNameNs ns cname TLNameTypeLC) magic

tokenIdentNs : TLNameType -> String -> TLToken
tokenIdentNs type s with (tokenSplitChar '.' s)
  tokenIdentNs type s | (Left name) = TLTokenIdent (MkTLName s type)
  tokenIdentNs type s | (Right (ns, name)) = TLTokenIdent (MkTLNameNs ns name type)

tokenMap : TokenMap TLToken
tokenMap = [
  tokenConstMap '_',
  tokenConstMap ':',
  tokenConstMap ';',
  tokenConstMap '(',
  tokenConstMap ')',
  tokenConstMap '[',
  tokenConstMap ']',
  tokenConstMap '{',
  tokenConstMap '}',
  (lcIdent <+> is '.' <+> digits, tokenCondDef),
  (exact "---", const TLTokenTripleMinus),
  (digits, tokenParseNat),
  (lcIdentFull, tokenIdentFull),
  (lcIdentNs, tokenIdentNs TLNameTypeLC),
  (ucIdentNs, tokenIdentNs TLNameTypeUC),
  tokenConstMap '=',
  tokenConstMap '#',
  tokenConstMap '?',
  tokenConstMap '%',
  tokenConstMap '+',
  tokenConstMap '<',
  tokenConstMap '>',
  tokenConstMap ',',
  tokenConstMap '.',
  tokenConstMap '*',
  tokenConstMap '!',
  (exact "Final", const TLTokenFinal),
  (exact "New", const TLTokenNew),
  (exact "Empty", const TLTokenEmpty),
  (space, const TLTokenSpace),
  (comment, TLTokenComment)
]

unneedTokens : TokenData TLToken -> Bool
unneedTokens (MkToken line col (TLTokenComment x)) = False
unneedTokens (MkToken line col TLTokenSpace) = False
unneedTokens (MkToken line col (TLTokenFail x)) = False
unneedTokens _ = True

export
tlLex : String -> List (TokenData TLToken)
tlLex str = let (tokens, col, line, left) = lex tokenMap str in
                filter unneedTokens tokens

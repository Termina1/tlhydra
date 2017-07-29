module TLInfer

import TLParserTypes
import TLTypes

export
convertAndInfer : TLSection -> TLDeclaration -> TLSCombinator
convertAndInfer section (Combinator x) = ?convertAndInfer_rhs_2
convertAndInfer section (BuiltInCombinator x) = ?convertAndInfer_rhs_3
convertAndInfer section (FinalDecl x y) = ?convertAndInfer_rhs_4

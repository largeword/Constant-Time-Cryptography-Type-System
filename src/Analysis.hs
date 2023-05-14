module Analysis
    ( analyse, TypeScheme(..)
    ) where

import AST
import Type
import TypeInference

analyse :: Expr -> Either String TypeScheme
analyse e = fmap fst (infer e) -- TODO: other analysis and transformations

module Analysis
    ( analyse, TypeScheme(..)
    ) where

import AST
import Type
import TypeInference

analyse :: Expr -> Either String TypeScheme
analyse = infer -- TODO: other analysis and transformations

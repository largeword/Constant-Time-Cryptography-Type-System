module Analysis
    ( analyse, TypeScheme(..)
    ) where

import AST
import Type
import TypeInference
import Debug.Trace (trace)

analyse :: Expr -> Either String TypeScheme
analyse e = fmap solve (infer e) -- TODO: other analysis and transformations
            where solve (ts, constr) = trace (show constr) ts

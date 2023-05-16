module Analysis
    ( analyse, TypeScheme(..)
    ) where

import AST
import Type
import TypeInference
import Debug.Trace (trace)
import Constraint (solve)

analyse :: Expr -> Either String TypeScheme
analyse e = infer e >>= solver -- TODO: other analysis and transformations
            where
                solver (ts, constr) = trace (show ts ++ "\n" ++ show constr) $ solve ts constr

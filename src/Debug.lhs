This defines some simple debugging facilities for Jaza, using Hood.
(See Observe.lhs/html for details).

To use it, import this Debug module (you must use hugs -98)
and replace any interesting

      val

by
      (observe "string" val)

Run the top-level program as: runO main

\begin{code}
module Debug
(
  module Observe
)
where
import AST
import Formatter
import Observe
import Subs

output_zexpr :: ZExpr -> String
output_zexpr = zexpr_string (pinfo_extz 75)

output_zpred :: ZPred -> String
output_zpred = zpred_string (pinfo_extz 75)

instance Observable ZExpr where
    observer e = send (output_zexpr e) (return e)

instance Observable ZPred where
    observer p = send (output_zpred p) (return p)

instance Observable ZGenFilt where
    observer g@(Check p) = send ("Check " ++ (output_zpred p)) (return g)
    observer g@(Choose x t) = send ("Choose " ++ show_zvar x ++ " "
				  ++ output_zexpr t)
				(return g)
    observer g@(Evaluate x e t) = send ("Evaluate " ++ show_zvar x ++ " "
				  ++ output_zexpr e ++ " "
				  ++ output_zexpr t)
				(return g)

instance Observable VarSet where
    observer vs = send ("{" ++ show_varset vs ++ "}") (return vs)

\end{code}

\section{Standard Laws}\label{ha:std-laws}
\begin{code}
module StdLaws where
import Utilities
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import CalcPPrint
import CalcTypes
import CalcPredicates
import CalcAlphabets
import CalcSimplify
import CalcRecogniser
import StdExpressions
import StdSets
import StdPredicates
\end{code}

We don't have a lot of laws here we want to invoked directly,
being too low-level for effective use of the calculator.
We just give a dictionary here for the standard composites.

\subsection{The Standard Dictionary}\label{hb:std-dict}

\begin{code}
stdDict :: Dict
stdDict
 = mergeDicts
    [ dictVersion "std 0.2"
    , stdExprDict
    , stdSetDict
    , stdPredDict
    ]
\end{code}

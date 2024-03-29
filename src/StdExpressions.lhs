\section{Standard Expressions}\label{ha:std-exprs}
\begin{code}
module StdExpressions where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Symbols
import Debug.Trace
import CalcPPrint
import CalcTypes
import CalcAlphabets
import StdPrecedences
import CalcPredicates
import DictAbstractions
\end{code}

Here we provide dictionary entries for all our ``standard''
 expression forms.

\subsection{Generic Definitions}\label{hb:gen-defs}


First, a application recogniser:
\begin{code}
isApp :: String -> Expr -> Bool
isApp aname (App nm _)  =  nm == aname
isApp _     _           =  False
\end{code}


\newpage
\subsection{Numeric Expressions}\label{hb:std-numberic}



\newpage
\subsubsection{Addition}\label{hc:def-And}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mAnd & \tAnd
}
\begin{code}
nAdd = "+" ; (mkAdd, addEntry) = opNonAssoc nAdd nAdd
nSub = "-" ; (mkSub, subEntry) = opNonAssoc nSub nSub
\end{code}


\begin{code}
stdExprDict :: Dict
stdExprDict
 = mergeDicts
    [ dictVersion "std-expr 0.1"
    , addEntry
    , subEntry
    ]
\end{code}

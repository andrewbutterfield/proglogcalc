\section{Calculator Demo}\label{sec:plc-demo}
\begin{code}
module PLCDemo where
import CalcTypes
import CalcPredicates
import CalcRun
import StdExpressions
import StdSets
import StdPredicates
import StdLaws
import StdUTPPredicates
import StdUTPLaws
\end{code}

We provide some facilities here to try out the calculator.


\subsection{``Standard'' Examples}


Tailor our display and calculator functions
to use our standard dictionary:
\begin{code}
std = dictshow stdDict
stdput = plainShow 80 stdDict
stdcalc = calcREPL stdDict noInvariants
\end{code}

Examples to come

\subsection{``Standard UTP'' Examples}

Merge standard predicate and UTP dictionaries:
\begin{code}
demoDict = stdUTPDict `dictMrg` stdDict
\end{code}

Tailor our display and calculator functions
to use our standard dictionary:
\begin{code}
utp = dictshow demoDict
utpput = plainShow 80 demoDict
utpcalc = calcREPL demoDict noInvariants
\end{code}

Examples to come

\subsection{Main}

We define a \texttt{help} function that simply prints out a quick guide.
\begin{code}
help
 = do putStrLn "\n\tPLCDemo\n"
      putStrLn
       $ unlines
          [ "std  -- displays standard predicate dictionary"
          , "stdput pred -- pretty-prints standard predicate"
          , "stdcalc pred -- starts calculation with standard predicate"
          , "---"
          , "utp -- displays UTP predicate dictionary"
          , "utpput pred -- pretty-prints UTP predicate"
          , "utpcalc pred -- starts calculation with UTP predicate"
          ]
\end{code}

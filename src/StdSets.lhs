\section{Standard Sets}\label{ha:Std-Sets}
\begin{code}
module StdSets where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import NiceSymbols
import Debug.Trace
import CalcPPrint
import CalcTypes
import CalcAlphabets
import CalcRecogniser
import StdPrecedences
import CalcPredicates
\end{code}

\begin{code}
-- import Debug.Trace
-- dbg str x = trace (str++show x) x
\end{code}



\subsubsection{Set Expressions}

We use sets in two key ways:
checking for membership/subset inclusion;
and updating by removing elements.
\begin{code}
setn = "set"
set = App setn

sngl e = set [e]

emp = set []

mkSet :: [Expr] -> Expr
mkSet = set . sort . nub

showSet d elms = "{" ++ dlshow d "," elms ++ "}"

evalSet _ _ = none

eqSet d es1 es2
 = let ns1 = nub $ sort $ es1
       ns2 = nub $ sort $ es2
   in if all (isGround d) (ns1++ns2)
      then Just (ns1==ns2)
      else Nothing
\end{code}

\begin{code}
evalSetBinFun op d [App nm1 es1,App nm2 es2]
 | nm1 == setn && nm2 == setn  =  op d es1   es2
evalSetBinFun _  _ _           =  none
\end{code}

We want some code to check and analyse both forms of singleton sets:
\begin{code}
isSingleton (App ns [_])  =  ns == setn
isSingleton _ = False

-- assumes isSingleton above
theSingleton (App _ [e])  =  e
\end{code}


\paragraph{Set Membership/Subset}\label{hd:membership}~

This is complicated by the fact we interpret
non-set expressions as singleton sets,
so $x \subseteq y$ when both are not sets
is considered to be $\setof x \subseteq \setof  y$
(which of course is really $x=y$).
\begin{code}
subsetn = _subseteq
subset e set = App subsetn [e,set]
evalSubset :: Dict -> [Expr] -> (String, Expr)
evalSubset = evalSetBinFun dosubset
dosubset d es1 es2 -- is es1 a subset of es2 ?
  | null es1lesses2  =  ( _subseteq, B True )
  | all (isGround d) (es1lesses2 ++ es2)
                     =  ( _subseteq, B False )
  | otherwise        =  none
  where
    es1lesses2 = es1 \\ es2
\end{code}

Set binary operator precedence ordering,
loosest to tightest:
$\cup,\cap,\setminus$.
\begin{code}
-- expression precedences not supported yet!
precUnion = precSpacer  11
precIntsc = precSpacer  12
precSDiff = precSpacer  13
\end{code}

\paragraph{Set Unary Operators}\label{hd:set-unops}~

We have set complement ($\overline S$),
where
\RLEQNS{
   \overline S &=& \mathcal U \setminus S
}
for some appropriate universe set $\mathcal U$.
\begin{code}
compn = _overline " "
complement s = App compn [s]
ppComp d [s] = _overline (edshow d s)
ppComp _ _ = "badd-comp"
\end{code}

\paragraph{Set Binary Operators}\label{hd:set-binops}~

\begin{code}
unionn = _cup
u s1 s2 = App unionn [s1,s2]
evalUnion :: Dict -> [Expr] -> (String, Expr)
evalUnion = evalSetBinFun dounion
dounion d es1 es2
  | all (isGround d) es1es2  =  ( _cup, mkSet es1es2 )
  | otherwise        =  none
  where
    es1es2 = es1 ++ es2
ppUnion d ss = "("  ++ dlshow d (pad _cup) ss ++ ")"
\end{code}

\begin{code}
intn = _cap
i s1 s2 = App intn [s1,s2]
evalIntsct :: Dict -> [Expr] -> (String, Expr)
evalIntsct= evalSetBinFun dointsct
dointsct d es1 es2
  | all (isGround d) es1es2  =  ( _cap, mkSet es1es2 )
  | otherwise        =  none
  where
    es1es2 = es1 `intersect` es2
ppIntsct d ss = "("  ++ dlshow d (pad _cap) ss ++ ")"
\end{code}


\begin{code}
sdiffn = _setminus
sdiff s1 s2 = App sdiffn [s1,s2]
evalSDiff :: Dict -> [Expr] -> (String, Expr)
evalSDiff = evalSetBinFun dosdiff
dosdiff d es1 es2
  | all (isGround d) es1es2  =  ( _setminus, mkSet es1es2 )
  | otherwise        =  none
  where
    es1es2 = es1 \\ es2
ppSDiff d ss = "("  ++ dlshow d (pad _setminus) ss ++ ")"
\end{code}

\paragraph{Set Utilities}

It can be useful to turn a set into a list
of its elements:
\begin{code}
setElems :: Expr -> [Expr]
setElems (App sn es) | sn == setn  =  sort $ nub $ es
setElems e = []
\end{code}
Also determining subsets (subsequences)
\begin{code}
isSubSeqOf [] _ = True
isSubSeqOf _ [] = False
isSubSeqOf a@(x:a') (y:b) | x==y       =  isSubSeqOf a' b
                          | otherwise  =  isSubSeqOf a  b
\end{code}
From GHC 7.10 onwards this is \texttt{Data.List.subSequencesOf}.



\begin{code}
showSubSet d [s1, s2]
 = "(" ++ edshow d s1
       ++  pad _subseteq
       ++ edshow d s2
       ++ ")"
\end{code}


The Set Dictionary:
\begin{code}
stdSetDict :: Dict
stdSetDict
 = mergeDicts
    [ dictVersion "std-set 0.1"
    , entry setn $ ExprEntry subAny showSet noDefn evalSet eqSet
    , entry compn $ ExprEntry subAny ppComp noDefn noEval noEq
    , entry unionn $ ExprEntry subAny ppUnion noDefn evalUnion noEq
    , entry intn $ ExprEntry subAny ppIntsct noDefn evalIntsct noEq
    , entry sdiffn $ ExprEntry subAny ppSDiff noDefn evalSDiff noEq
    , entry subsetn $ ExprEntry subAny showSubSet noDefn evalSubset noEq
    ]
\end{code}

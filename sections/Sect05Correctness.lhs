%if False
\begin{code}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Sect05Correctness where

import Sect02SemStd

data SymbolicValue where      -- fake
data Thread_s :: * -> * where -- fake
data Config_s :: * -> * where -- fake

\end{code}
%endif

\section{Correctness}

\label{sec:correctness}

We have shown how to derive a symbolic executor from a concrete semantics.
The derivation was driven by an intuitive understanding of what needs to happen in a symbolic executor (instantiating and refining symbolic variables, forking new threads of interpretation) in order to ensure that the symbolic executor explores \emph{all possible execution paths}, but \emph{only} possible execution paths (i.e., no execution paths that do not correspond to an actual execution path).
In this section we conjecture a correctness proposition for our symbolic evaluator, and discuss directions for making this correctness proposition more formal.

Let |runSteps_s| be a function that uses the |drive_s| function to drive an expression to a final value and pool of alternative execution paths that may yet yield a final result:
\begin{code}
runSteps_s ::  Expr -> Env SymbolicValue ->
               Either String  (SymbolicValue,
                              [Config_s (Thread_s SymbolicValue)])
\end{code}
%if False
\begin{code}
runSteps_s = error "fake"
\end{code}
%endif
We conjecture that, for any pair of concrete environment |nv| and symbolic environment |nv_s| that are equal up-to-unification:
\begin{enumerate}
\item Any concrete execution path, given by calling |runSteps| from \cref{sec:towards-sym-exc} under |nv| with any |e :: Expr| either yields a value that is equal up-to-unification to the |SymbolicValue| that |runSteps_s| returns; or yields a value that one of the configurations in |runSteps_s| will eventually yield, if we were to iterate that configuration.
\item Any symbolic execution path, given by calling |runSteps_s| under |nv_s| with any |e :: Expr| yields a symbolic value and set of configurations that exhaustively describe any concrete execution path resulting from evaluating |e| under any |nv'| that is equal up-to-unification to |nv_s|.
\end{enumerate}

We believe that \emph{abstract interpretation} \cite{CousotC77} is a suitable framework for formalizing the correspondence between concrete and symbolic execution.\footnote{Indeed, it seems \citet{Cousot78} has considered how to formalize symbolic execution within the framework of abstract interpretation.  This formalization is only available in French \cite{42290}.}
The methodology due to \citet{KeidelPE18} for defining static analyzers with compositional soundness proofs is attractive to consider for this purpose.
But it is an open question how the small-step interpretation strategy based on free monads that we adopted in \cref{sec:towards-sym-exc} and \cref{sec:sym-exc} to realize our symbolic executor fits into the framework and methodology of \citet{KeidelPE18}.
In very recent work, \citet{RozplokhasVB19} provide a certified definition of miniKanren.
In future work, we will investigate how to port their verification technique to the development in this paper.

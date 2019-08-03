\section{Introduction}

Symbolic execution is a meta-programming technique that is at the core of techniques for boosting developer productivity, such as the \emph{automated testing}~\cite{GodefroidKS05,SenMA05,CadarDE08,GiantsiosPS17,BucurKC14} and \emph{program synthesis}~\cite{GulwaniPS17,OseraZ15,Eguchi0T18}.
A symbolic executor allows exploration of possible execution paths by running a program with symbolic variables in place of concrete values.
By strategically instantiating symbolic variables, a symbolic executor can be used to systematically analyze which parts of a program are reachable, with which inputs.

Constructing symbolic executors is non-trivial, and enabling support for symbolic execution for general-purpose languages, such as C~\cite{GodefroidKS05,SenMA05,BurnimS08}, C++~\cite{LiGR11}, Java~\cite{SenA06,AnandPV07}, PHP~\cite{ArtziKDTDPE10}, or Rust~\cite{LindnerAL18}, is the topic of entire publications at major software engineering conferences.
We propose that techniques for symbolic execution are reusable between languages, and in this paper we investigate the foundations of how to define and implement symbolic executors, by systematically deriving them from \emph{definitional interpreters}.
Our long-term goal is to integrate these techniques into a language workbenches, such as Spoofax~\cite{KatsV10}, Rascal~\cite{KlintSV09}, or Racket~\cite{FelleisenFFKBMT15}, to enable the automatic generation of programmer productivity boosting tools, such as automated testing frameworks and program synthesizers.

\paragraph{In this paper} we explore how to mechanically derive a symbolic executors that explores possible execution paths through programs by instantiating and specializing symbolic variables, following a breadth-first search strategy that interleavingly executes a program along all possible execution paths.
Our exploration revolves around a dynamically-typed language with recursive functions and pattern matching.
Using Haskell as our meta-language, and working with its integrated support for generic and monadic programming, we implement a definitional interpreter for this language.
This definitional interpreter is parameterized by an interface which we instantiate in two different ways to obtain first a concrete interpreter, and then a symbolic executor for the language.

The symbolic executor we derive supports solving constraints such as the following:
\begin{center}
|append l [4,5] == [1, 2, 3, 4, 5]|
\end{center}
Symbolic execution runs the |append| function by systematically exploring all possible instantiations of the symbolic variable |l|, and checking which instantiation yield a valid end result that matches the list |[1, 2, 3, 4, 5]|, to conclude that |l == [1, 2, 3]|.
This paper is a literate Haskell file, and we invite interested readers to download the Haskell version of the paper to experiment with, and extend, the framework we present.\footnote{\url{https://github.com/MetaBorgCube/From-Definitional-Interpreter-To-Symbolic-Executor}}

\paragraph{Related Previous Lines of Work}
The techniques that we develop in this paper are closely related to the techniques used for \emph{relational programming}, pioneered by Byrd and Friedman in (Mini)Kanren \cite{Byrd2010thesis,ByrdHF12,Hemann13microKanren}.
MiniKanren is a mature framework for symbolically executing Scheme programs implemented in a relational style, has a reasonably efficient run time, and guiding the exploration of possible execution paths by means of sophisticated heuristics~\cite{LuMF19}.
MiniKanren has recently been ported to other languages, such as OCaml~\cite{Kosarev2016typedembedding}.
In this paper we pursue the goal of deriving symbolic executors from definitional interpreters in general, to bring the benefits of relational programming and MiniKanren to programming languages at large.

We are working with Haskell as our meta-language, which provides support for various libraries and monads for non-determinism and logic programming, notably in the work of \citet{Kiselyov2005backtracking}.
This paper draws inspiration from these techniques in order to implement a symbolic executor, but we are not aware of any existing libraries or monads in Haskell for supporting the kind of breadth-first search over possible execution paths that we use in this paper for symbolic execution.

There has been much work on symbolic execution in the literature on software engineering; e.g.,~\cite{GodefroidKS05,SenMA05,BurnimS08,LiGR11,SenA06,AnandPV07,ArtziKDTDPE10,LindnerAL18}. 
Many of these frameworks are so-called \emph{concolic} frameworks that work by instrumenting a concrete language runtime to track \emph{symbolic path constraints}.
After each concrete execution, these path constraints are collected and solved in order to cover a different path through the program in a subsequent run of the program.
Concolic testing is typically implemented by generating test inputs randomly, rather than systematically solving path constraints.
In this paper, we explore a symbolic execution strategy which interleavingly explores multiple execution paths concurrently, rather than a concolic testing approach, as concolic testing would require a relatively sophisticated constraint solver in order to explore execution paths in an equally systematic manner.


\paragraph{Contributions} We contribute:
\begin{itemize}
\item Techniques (in \cref{sec:towards-sym-exc}) for deriving symbolic executors from definitional interpreters, by using \emph{free monads} to compile programs into \emph{command trees}, and interpreting these trees using a small-step execution strategy.
\item A symbolic executor (in \cref{sec:sym-exc}) for a language with algebraic datatypes that illustrates these techniques.
\item A simple example application (in \cref{sec:case-study}): automated test generation for definitional interpreters.
\end{itemize}

The rest of this paper is structured as follows.
In \cref{sec:def-interp} we introduce a definitional interpreter for a language with recursion and pattern matching.
In \cref{sec:towards-sym-exc} we present a definitional interpretation of the effects, by means of a free monad, using a small-step semantics execution strategy.
In \cref{sec:sym-exc} we generalize the definitional interpretation of effects from \cref{sec:towards-sym-exc}, to obtain a symbolic executor, whose correctness we discuss in \cref{sec:correctness}.
Finally, in \cref{sec:case-study} we discuss a case study application of the symbolic executor: generating tests for definitional interpreters. \Cref{sec:conclusion} concludes.




%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../document"
%%% End:


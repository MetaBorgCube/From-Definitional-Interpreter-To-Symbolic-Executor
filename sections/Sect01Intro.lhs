\section{Introduction}

Symbolic execution~\cite{King76} is a meta-programming technique that is at the core of techniques for boosting developer productivity, such as \emph{automated testing}~\cite{GodefroidKS05,SenMA05,CadarDE08,GiantsiosPS17,BucurKC14} and \emph{program synthesis}~\cite{OseraZ15,GulwaniPS17,Eguchi0T18}.
A symbolic executor allows exploration of possible execution paths by running a program with symbolic variables in place of concrete values.
By strategically instantiating symbolic variables, a symbolic executor can be used to systematically analyze which parts of a program are reachable, with which inputs.

Constructing symbolic executors is non-trivial, and enabling support for symbolic execution for general-purpose languages, such as C~\cite{GodefroidKS05,SenMA05,BurnimS08}, C++~\cite{LiGR11}, Java~\cite{SenA06,AnandPV07}, PHP~\cite{ArtziKDTDPE10}, or Rust~\cite{LindnerAL18}, is the topic of entire publications at major software engineering conferences.
We propose that techniques for symbolic execution are reusable between languages, and investigate the foundations of how to define and implement symbolic executors, by deriving them from \emph{definitional interpreters}.
Our long-term goal is to integrate these techniques into language workbenches, such as Spoofax~\cite{KatsV10}, Rascal~\cite{KlintSV09}, or Racket~\cite{FelleisenFFKBMT15}, to enable the automatic generation of programmer productivity boosting tools, such as automated testing frameworks and program synthesizers.

In this paper we explore how to mechanically derive symbolic executors that explore possible execution paths through programs by instantiating and specializing symbolic variables, following a breadth-first search strategy.
Our exploration revolves around a dynamically-typed language with recursive functions and pattern matching.
Using Haskell as our meta-language, and working with its integrated support for generic and monadic programming, we implement a definitional interpreter for this language.
This definitional interpreter is parameterized with an interface which we instantiate in two different ways to obtain first a concrete interpreter, and then a symbolic executor.
The ``derivation'' thus amounts to instantiating the interface operations in a manner that yields a symbolic executor.

The symbolic executor we derive allows us to explore the solution space for constraints such as the following constraint that a list |xs| must be a palindrome:
\begin{center}
|xs == reverse xs|
\end{center}
Symbolic execution explores all execution paths through the |reverse| function that satisfy the constraint, and instantiates |xs| accordingly, thereby generating palindromes.
This paper is a literate Haskell file, and we invite interested readers to download the Haskell version of the paper to experiment with, and extend, the framework we present.\footnote{\url{https://github.com/MetaBorgCube/From-Definitional-Interpreter-To-Symbolic-Executor}}

\paragraph{Related Previous Lines of Work}
The techniques that we develop in this paper are closely related to the techniques used for \emph{relational programming}, pioneered by Friedman and Byrd in miniKanren~\cite{FriedmanBO05,Byrd2010thesis,ByrdHF12,Hemann13microKanren}, a language for relational programming and constraint logic programming, which has been implemented in a wide range of different languages; notably Scheme~\cite{FriedmanBO05,ByrdF06}, but also, e.g., OCaml~\cite{Kosarev2016typedembedding}.
The miniKanren language and many of its implementations have been developed and researched for more than a decade, with new developments and improvements appearing each year, such as new and better heuristics for guiding the exploration of execution paths~\cite{LuMF19}.
The motivation for this paper is to bring similar benefits as found in miniKanren to programming languages at large, by automatically deriving symbolic executors from definitional interpreters.

Rosette~\cite{TorlakB13,TorlakB14} is a solver-aided language that extends Racket~\cite{FelleisenFFKBMT15} to provide framework for implementing solver-aided domain-specific languages, by means of a symbolic virtual machine and symbolic compiler.
This VM brings the benefits of symbolic execution and model checking to languages implemented in Rosette via general-purpose symbolic abstractions that support sophisticated symbolic reasoning, beyond the relatively simple constraints found in (most variants of) miniKanren.
A main goal of Rosette is to implement solver-aided languages, but the symbolic abstractions and techniques that Rosette implements could also be used to address the problem that is the motivation for this paper, namely the problem of automatically deriving symbolic executors from ``traditional'' definitional interpreters.

There has been much work on symbolic execution in the literature on software engineering; e.g.,~\cite{GodefroidKS05,SenMA05,BurnimS08,LiGR11,SenA06,AnandPV07,ArtziKDTDPE10,LindnerAL18}. 
Many of these frameworks are so-called \emph{concolic} frameworks that work by instrumenting a concrete language runtime to track \emph{symbolic path constraints}.
After each concrete execution, these path constraints are collected and solved in order to cover a different path through the program in a subsequent run of the program.
Concolic testing is typically implemented by generating test inputs randomly, rather than systematically solving path constraints.
In this paper, we explore a symbolic execution strategy which interleavingly explores multiple execution paths concurrently, rather than a concolic testing approach which would require a relatively sophisticated constraint solver in order to explore execution paths in an equally systematic manner.

\paragraph{Contributions}
\begin{itemize}
\item Techniques (in \cref{sec:towards-sym-exc}) for deriving symbolic executors from definitional interpreters, by using \emph{free monads} to compile programs into \emph{command trees}, and interpreting these using a small-step execution strategy.
\item A symbolic executor (in \cref{sec:sym-exc}) for a language with algebraic datatypes that illustrates these techniques.
\item A simple example application (in \cref{sec:case-study}): automated test generation for definitional interpreters.
\end{itemize}

The rest of this paper is structured as follows.
In \cref{sec:def-interp} we introduce a definitional interpreter for a language with recursion and pattern matching.
In \cref{sec:towards-sym-exc} we present a definitional interpretation of the effects, by means of a free monad, using a small-step semantics execution strategy.
In \cref{sec:sym-exc} we generalize the definitional interpretation of effects from \cref{sec:towards-sym-exc}, to obtain a symbolic executor, whose correctness we discuss in \cref{sec:correctness}.
Finally, in \cref{sec:case-study} we discuss a case study application of the symbolic executor: generating tests for definitional interpreters, and \Cref{sec:conclusion} concludes.




%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../document"
%%% End:


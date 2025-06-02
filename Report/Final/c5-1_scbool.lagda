%if False
\begin{code}
{-# OPTIONS --prop --rewriting #-}

open import Utils hiding (ε)
open import Utils.IdExtras

module Report.Final.c5-1_scbool where

\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{A Minimal Language with Smart Case}
\labch{scbool}

\newcommand{\SCBool}{$\textsf{SC}^\textsc{Bool}$\xspace}

In this chapter, we introduce and study a minimal dependently-typed language
featuring a \SC-like elimination principle for Booleans. We name
this language \SCBool. We will also detail the core ideas behind my Haskell
typechecker for an extended version of this language.

\section{Syntax}

\section{Soundness}

\section{Normalisation Challenges}

\section{Typechecking Smart Case}

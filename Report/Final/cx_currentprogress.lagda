%if False
\begin{code}
{-# OPTIONS --prop --guardedness #-}

open import Utils renaming (_+ℕ_ to _+_)
import Relation.Binary.PropositionalEquality as EQ
open EQ.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎)
open import Common.Sort

module Report.Interim.cx_currentprogress where
\end{code}
%endif

\setchapterpreamble[u]{\margintoc}

\chapter{Current Progress}
\labch{progress}

\section{STLC with Boolean Rewrites}

\section{Dependent Type Theory with Equational Assumptions}
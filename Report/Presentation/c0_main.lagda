%if False
\begin{code}
{-# OPTIONS --prop #-}

module Report.Presentation.c0_main where

open import Utils hiding (Bool-split; f3)

variable
  A : Set
  x₁ x₂ : A
\end{code}
%endif

%let intrinsic_style = True

\documentclass{beamer}

\usepackage[style=authoryear,backend=biber]{biblatex}
\addbibresource{main.bib}

\usepackage{xpatch}
\xapptobibmacro{cite}{\setunit{\nametitledelim}\printfield[emph]{title}}{}{}
% TODO: I would like to also put the year in parens, but this is tricky
% There doesn't appear to be a way to just overwrite a bibmacro completely
%\xpatchbibmacro{cite}{\printfield{author} (\printfield{year}), \printfield[emph]{title}}{}{}


% Remove some unwanted entries from the bibliography
\AtEveryBibitem{
	\clearfield{issn}
	\clearfield{isbn}
	\clearfield{archivePrefix}
	\clearfield{arxivId}
	\clearfield{pmid}
	\clearfield{eprint}
	% I want URLs!
	% \ifentrytype{online}{}{\ifentrytype{misc}{}{\clearfield{url}}}
	% But not if there is a doi!
	\iffieldundef{doi}{}{\clearfield{url}}
	% I also want DOIs!
	% \ifentrytype{book}{\clearfield{doi}}{}

}

\title{Local Rewriting in Dependent Type Theory}
\author{Nathaniel Burke}
\institute{Imperial Computing Final Year Project Presentation}
\date{2025}

\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{latexsym}

\usepackage[theoremfont,libertinus,smallerops,vvarbb]{newtx}
\usepackage[scaled=.85]{beramono}
\usepackage[scr=rsfso,cal=boondoxo]{mathalfa}
\usepackage{morewrites}

\usefonttheme[onlymath]{serif}

\usepackage[only,llbracket,rrbracket]{stmaryrd}

\let\refeq\relax
\usepackage{mathtools}

\usepackage{dsfont}
\newcommand\hmmax{0}
\newcommand\bmmax{0}
\usepackage{bm}

\usepackage{xspace}
\usepackage[dvipsnames]{xcolor}

% From https://tex.stackexchange.com/questions/262878/how-to-horizontal-vertical-combine-two-math-symbols
\providecommand*\colonequiv{\vcentcolon\mspace{-1.2mu}\equiv}

%include lhs2TeX.fmt
%%include polycode.fmt
%include agda_tweaked.fmt
%include lib.fmt

\setbeamertemplate{itemize subitem}{|∙|}

\begin{document}

\newcommand{\smart}{\textsf{\textbf{smart}}\xspace}
\newcommand{\SC}{\textsf{\textbf{smart case}}\xspace}
\newcommand{\SIF}{\textsf{\textbf{smart if}}\xspace}
\newcommand{\SCBool}{$\textsf{SC}^{\textsc{Bool}}$\xspace}
\newcommand{\SCDef}{$\textsf{SC}^{\textsc{Def}}$\xspace}

\newcommand{\nocodeindent}{\setlength\mathindent{0em}}
\newcommand{\resetcodeindent}{\setlength\mathindent{1em}}
\newcommand{\nobarfrac}{\gendfrac{}{}{0pt}{}}

\nocodeindent

\newcommand{\footnocite}[1]{\phantom{\footcite{#1}}}

% From https://tex.stackexchange.com/questions/13793/beamer-alt-command-like-visible-instead-of-like-only
% \newcommand<>\Alt[2]{{%
%     \sbox0{#1}%
%     \sbox1{#2}%
%     \alt#3%
%         {\rlap{\usebox0}\vphantom{\usebox1}\hphantom{\ifnum\wd0>\wd1 \usebox0\else\usebox1\fi}}%
%         {\rlap{\usebox1}\vphantom{\usebox0}\hphantom{\ifnum\wd0>\wd1 \usebox0\else\usebox1\fi}}%
% }}

\newcommand<>{\altvphantom}[2]{\alt#3{#1}{#2}\vphantom{#1}\vphantom{#2}}


\frame{\titlepage}

%TODO: Maybe add a motivation slide...

\begin{frame}
\frametitle{Motivation}
\begin{itemize}
\item<1-3> \textbf{Dependent Type Theory:} Foundation of many proof 
      assistants and 
      cutting-edge programming languages
      \begin{itemize}
      \item \textbf{Expressive:} Scales to modern mathematics
      \footcite{escardo2025topology, buzzard2025flt} and metamathematics
      (including the study of type theory itself
      \footcite{pujet2022observational, abel2023graded})
      \end{itemize}    
\item<2-3> Allows us to precisely specify and verify programs
      \begin{itemize}
      \item E.g. |Π x ∶ ℕ, y ∶ ℕ. x + y ≡' y + x|
      \end{itemize}
\item<3> \textbf{Drawback:} Limited automation, especially with respect to
      equational reasoning
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Manual Equational Reasoning in Proof Assistants}

\centering \Large
\emph{Demo...}
\end{frame}

\begin{frame}
\frametitle{``Transport Hell''}

\begin{itemize}
\item<1-4> \emph{Indexed datatypes} often require equational reasoning 
      mutual with the implementation of operations (\emph{transport}).
\item<2-4> |Fin n|, |Vec A n|, |Tm Γ A| etc... 
\item<3-4> When proving laws about these operations, we have to account for
      these transports, using painful lemmas like \footcite{2024propprop}:
      \uncover<4>{
      \begin{code}
transp-application  : ∀  (B : A → Set) {C : A → Set}
                         {y} (g : ∀ x → B x → C x) 
                         (p : x₁ ≡ x₂) 
                    →  subst C p (g x₁ y) 
                    ≡  g x₂ (subst B p y)
      \end{code}}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Contribution}
\centering \Large
\emph{Demo...}
\normalsize
\vspace{8ex}
\begin{itemize}
\item<2-4> A new type theory where the built-in
equality (\emph{conversion}) is defined modulo a set of local equations.
\item<3-4> To decide conversion, we now rely on techniques from  
      \emph{term rewriting}.
\item<4> Concrete contributions include formal results (proofs!) and
      a prototype typechecker implementation.
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Local Equality Reflection}
\begin{itemize}
\item<1-4> \textbf{Idea:} Extend contexts with equational assumptions.
\item<2-4> Reflecting arbitrary propositional equations is very powerful,
      but breaks decidability of typechecking.
      \alt<4>{
      \[
      \frac{\begin{matrix}
      |⊢ Γ ctx|,\quad |Γ ⊢ A, B type'|,\quad |Γ ⊢ t₁, t₂ ∶ A|\\
      |Γ ⊢ p ∶ (t₁ ≡' t₂)|\\
      |(Γ ▷ t₁ ~ t₂) ⊢ u ∶ B|
      \end{matrix}}
      {|Γ ⊢ reflect p in' u ∶ B|}\]
      }{
      \[
      \frac{\begin{matrix}
      |Γ : Ctx|,\quad |A, B : Ty Γ|,\quad |t₁, t₂ : Tm Γ A|\\
      |p : Tm Γ (t₁ ≡' t₂)|\\
      |u : Tm (Γ ▷ t₁ ~ t₂) B|
      \end{matrix}}
      {|reflect p in' u : Tm Γ B|}\]
      }

%     %if intrinsic_style
%     \[
%     \frac{\begin{matrix}
%     |Γ : Ctx|,\quad |A, B : Ty Γ|,\quad |t₁, t₂ : Tm Γ A|\\
%     |p : Tm Γ (t₁ ≡' t₂)|\\
%     |u : Tm (Γ ▷ t₁ ~ t₂) B|
%     \end{matrix}}
%     {|reflect p in' u : Tm Γ B|}\]
%     %else
%     \[
%     \frac{\begin{matrix}
%     |⊢ Γ ctx|,\quad |Γ ⊢ A, B type'|,\quad |Γ ⊢ t₁, t₂ ∶ A|\\
%     |Γ ⊢ p ∶ (t₁ ≡' t₂)|\\
%     |(Γ ▷ t₁ ~ t₂) ⊢ u ∶ B|
%     \end{matrix}}
%     {|Γ ⊢ reflect p in' u ∶ B|}\]
%     %endif
\item<3-4> Need to restrict equations somehow...
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{``Smart Case''}
\textbf{Starting Point:} Equations arising from (Boolean) case splits 
\footcite{altenkirch2011case}
%if intrinsic_style
\[
\frac{\begin{matrix}
|Γ : Ctx|,\quad |t : Tm Γ 𝔹|,\quad |A : Ty Γ|\\
|u : Tm (Γ ▷ t ~ TT) A|\\
|v : Tm (Γ ▷ t ~ FF) A|
\end{matrix}}
{|sif t then u else v : Tm Γ A|}\]
%else
\[
\frac{\begin{matrix}
|⊢ Γ ctx|,\quad |Γ ⊢ t ∶ 𝔹|,\quad |Γ ⊢ A type'|\\
|(Γ ▷ t ~ TT) ⊢ u ∶ A|\\
|(Γ ▷ t ~ FF) ⊢ v ∶ A|
\end{matrix}}
{|Γ ⊢ sif t then u else v ∶ A|}\]
%endif
The scrutinee and pattern are convertible in each branch.
\end{frame}

\begin{frame}
\frametitle{A Substitution Calculus for Contextual Equations (\SCBool)}
\begin{itemize}
\item<1-3> Mapping from the empty context is trivial.
      \[\frac{}
      {|ε : Tms Δ •|}\]   
\item<2-3> To map from a context extended with a variable, 
      we need to provide a substitute term.
      \[\frac{|δ : Tms Δ Γ|,\quad |t : Tm Δ (A [ δ ]Ty)|}
      {|δ , t : Tms Δ (Γ ▷ A)|}\]
\item<3> To map from a context extended with an equation, 
      we need to provide
      substitute \emph{evidence of convertibility}. (\textbf{New!})
      \[\frac{|δ : Tms Δ Γ|,\quad |p : t₁ [ δ ] ~Tm t₂ [ δ ]|}
      {|δ ,eq p : Tms Δ (Γ ▷ t₁ ~ t₂)|}\]
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Normalisation by Evaluation 
(NbE)\footnocite{berger1991inverse}
\footnocite{altenkirch2017normalisation}}
\begin{itemize}
\item<1-4> \textbf{Aim:} Associate a canonical representative (``normal form'')
      with every equivalence class of terms.
\item<2-4> \textbf{Idea:} Construct a model (\emph{evaluation}) and invert 
      it (\emph{quotation}).\\|norm t = quote (eval idℰ t)|
\item<3-4> \textbf{Soundness:} Conversion is preserved during evaluation and 
      quotation.\\|t ~Tm u → norm t ≡ norm u|
\item<4> \textbf{Completeness:} Equality 
      of normal forms implies convertibility
      of original terms (conservative).\\
      |norm t ≡ norm u → t ~Tm u|
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{NbE for \SCBool: Inconsistent Contexts}
\begin{itemize}
\item<1-3> All types are \emph{propositionally} equal under 
      \emph{propositionally} inconsistent contexts, e.g.
      |Γ = p ∶ (TT ≡' FF)|.
      \begin{itemize}
      \item Normalisation retained---transport blocks computation
      \end{itemize}
\item<2-3> \emph{Definitionally} inconsistent contexts are more dangerous!
      \\In 
      |Γ = b ∶ 𝔹 , b ~ TT , b ~ FF|, ``|(ƛ x. x x) (ƛ x. x x)|'' is typeable.
      \vspace{-4ex}
      \begin{spec}
    A
==  if TT then A else (A ⇒ A)
==  if FF then A else (A ⇒ A)
==  (A ⇒ A)
      \end{spec}
      \vspace{-4ex}
\item<3> Need to avoid evaluating under (\emph{definitionally}) 
      inconsistent contexts.
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{NbE for \SCBool: Completion}
\begin{itemize}
\item<1-2> Deciding context inconsistency is non-trivial! 
      \begin{itemize}
      \item LHSs might be reducible: |(ƛ x. x) b ~ TT , b ~ FF|
      \item LHSs might overlap:\hspace{18.5pt} |not b ~ TT , b ~ TT| 
      \end{itemize}  
\item<2> The appropriate technique here is 
      \emph{completion}\footcite{baader1998term}. 
      \begin{itemize}
      \item Aims to transform a set
            of equations into a \emph{confluent} term rewriting system (TRS).
      \item \textbf{Confluence:} |t >* u| and |t >* v| implies existence
            of a term, |w|, such that |u >* w| and |v >* w|. 
      \item Needs a well-founded order... 
      \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{NbE for \SCBool: Challenges}
\begin{itemize}
\item<1-4> \textbf{Idea:} Avoid completion by enforcing that LHSs are 
      irreducible and disjoint (syntactic restriction).

\item<2-4> \textbf{Doesn't Work!} Unstable under substitution!\\
      |Γ = x ∶ 𝔹 , y ∶ 𝔹 , x ~ TT , y ~ FF|
% \item So, incompatible with most existing proof assistants (β-conversion).
\item<3-4> Stability-under-substitution also rules out a lot of more interesting
      equations (beyond Booleans).
\item<4> \textbf{Further Difficulties:} 
      Evaluation must recurse into the branches of \SIF.
      \begin{itemize}
      \item Need to interleave evaluation and completion.
      \item Normal forms (also values) are not stable under extending the 
            context with equations.
      \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}
\vspace*{\fill}
\centering
\usebeamerfont{frametitle}\usebeamercolor[fg]{frametitle} 
Recovering Normalisation via Elaboration
\vspace*{\fill}
\end{frame}
%\frame{\vspace*{\fill}\insertframetitle AAA\vspace*{\fill}}

\begin{frame}
\frametitle{Elaborating Case Splits to Top-Level Definitions}

Already implemented in Agda\footcite{agda2024with, agda2024lambda}

%if False
\begin{code}
data Cmp : Set where
  gt eq lt : Cmp
_<_ : ℕ → ℕ → Bool
_>_ : ℕ → ℕ → Bool
\end{code}
%endif

\begin{minipage}{0.5\textwidth}
\begin{code}
cmp : ℕ → ℕ → Cmp
cmp n m  with n > m
cmp n m  | true   = gt
cmp n m  | false  with n < m
cmp n m  | false  | true   = lt
cmp n m  | false  | false  = eq
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{spec}
data Cmp : Set where
  gt  : Cmp
  eq  : Cmp
  lt  : Cmp
\end{spec}
\end{minipage}


%if False
\begin{code}
cmp-aux₂ : ℕ → ℕ → Bool → Cmp
cmp-aux₁ : ℕ → ℕ → Bool → Cmp
cmp-elab : ℕ → ℕ → Cmp
\end{code}
%endif
\uncover<4>{
\begin{code}
cmp-aux₂ n m true   = lt
cmp-aux₂ n m false  = eq
\end{code}}
\vspace{-5ex}
\uncover<3-4>{
\begin{code}
cmp-aux₁ n m true   = gt
cmp-aux₁ n m false  = cmp-aux₂ n m (n < m)
\end{code}}
\vspace{-5ex}
\uncover<2-4>{\begin{code}
cmp-elab n m = cmp-aux₁ n m (n > m)
\end{code}}
\end{frame}

\begin{frame}
\frametitle{Elaborating Case Splits to Top-Level Definitions (\SCDef)}

% TODO: Is a good idea to use different syntax for SCBool/SCDef??
\begin{spec}
f3 ∶ ∀ (f : Bool → Bool) → f true ≡ f (f (f false))
f3 f = sif (f true) then refl else (sif (f false) then refl else refl)
\end{spec}

Becomes...

\uncover<4>{\begin{spec}
f3-aux₂  : ∀ (f : Bool → Bool) (f true == false) | f false 
         → f true ≡ f (f (f true))
f3-aux₂ f | true   = refl
f3-aux₂ f | false  = refl
\end{spec}}
\vspace{-5ex}
\uncover<3-4>{\begin{spec}
f3-aux₁  : ∀ (f : Bool → Bool) | f true
         → f true ≡ f (f (f true))
f3-aux₁ f | true   = refl
f3-aux₁ f | false  = call f3-aux₂ f
\end{spec}}
\vspace{-5ex}
\uncover<2-4>{\begin{spec}
f3-elab : ∀ (f : Bool → Bool) → f true ≡ f (f (f true))
f3-elab = call f3-aux₁ f
\end{spec}}
\end{frame}

\begin{frame}
\frametitle{Elaborating Case Splits to Top-Level Definitions (\SCDef)}

Two new ingredients:
\begin{itemize}
\item<2-3> Parameter lists (\emph{telescopes}) of definitions now 
      include convertibility constraints.
% \begin{itemize}
% \item (Almost) free via the earlier substitution calculus (telescopes are
%       contexts, parameters are substitutions)!
% \end{itemize}  
\item<3> Definitions block on neutrals, and reflect appropriate equations. 
\end{itemize}


%\[\dfrac{\begin{matrix}
%|Ξ : Sig|\quad |Γ : Ctx Ξ|\quad |A, B : Ty Γ|\\
%|t₁, t₂ : Tm Γ A|\quad |p : Tm Γ (t₁ ≡' t₂)|\\
%|u : Tm (Γ ▷ t₁ ~ t₂) B|
%\end{matrix}}
%{|(Ξ ▷ Γ ⇒ B reflects p in' u) : Sig|}\]

\uncover<3>{
%if intrinsic_style
\[\dfrac{\begin{matrix}
|Ξ : Sig|\quad |Γ : Ctx Ξ|\quad |A : Ty Γ|\quad |t : Tm Γ 𝔹|\\
|u : Tm (Γ ▷ t ~ TT)  A|\\
|v : Tm (Γ ▷ t ~ FF)  A|
\end{matrix}}
{|(Ξ ▷ Γ ⇒ A sif t then u else v) : Sig|}\]
%else
\[\dfrac{\begin{matrix}
|⊢ Ξ sig|\quad |Ξ ⊢ Γ ctx|\quad |Γ ⊢ A type'|\quad |Γ ⊢ t ∶ 𝔹|\\
|(Γ ▷ t ~ TT) ⊢ u ∶ A|\\
|(Γ ▷ t ~ FF) ⊢ v ∶  A|
\end{matrix}}
{|⊢ (Ξ ▷ Γ ⇒ A sif t then u else v) sig|}\]
%endif
}
\end{frame}

\begin{frame}
\frametitle{Have We Lost Anything?}

\begin{itemize}
\item<1-2> Congruence of conversion! Sort of...
      \begin{itemize}
      \item Distinct case splits are elaborated to different top-level 
      auxiliary definitions.
      \item Definitions only reduce after the new equation holds
      ``on-the-nose''.
      \item So stuck calls to distinct definitions are never convertible (even if
            the bodies are).
      \end{itemize}
\item<2> Convertibility of \emph{core terms} is still congruent though!
      \[\dfrac{
      |f₁ ~DVar f₂|\quad |δ₁ ~Tms δ₂|}
      {|call f₁ δ₁ ~Tm call f₂ δ₂|}\] 
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Normalisation is Easy(er)!}

\begin{itemize}
\item<1-3> Evaluation can now be defined w.r.t. a single completed TRS.
      \begin{itemize}
      \item Evaluation halts when it encounters blocked |call| expressions.
      \end{itemize}
\item<2-3> Unquoting looks up neutral terms in the TRS.
\item<3> We still need to obtain the completed TRS in the first place...
      \begin{itemize}
      \item But, we can now restrict equations however we like!
      \item One possible strategy: require that LHSs are disjoint
            post-normalisation under the prior set of equations.
      \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Conclusion}
\begin{itemize}
\item<1-4> Introduced \SCBool: a type theory with contextual equations
      and \SIF.
      \begin{itemize}
      \item Proved soundness (consistency relative to MLTT) by constructing
            a model
      \end{itemize}
\item<2-4> Introduced \SCDef: a type theory where equations are reflected
      at top level definitions.
      \begin{itemize}
      \item Also proved soundness, and decidability of conversion
            (via normalisation by evaluation)
      \end{itemize}
\item<3-4> Implemented prototype \SCBool typechecker in Haskell
\item<4> Formal results are mostly mechanised in Agda
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Future Work}
\begin{itemize}
\item<1-2> Support a wider class of equations
      \begin{itemize}
      \item Neutral RHSs and neutral-typed
      \item Inductive types (occurs check!)
      \item Non-disjoint LHSs (via completion - would need to find a 
            well-founded order)
      \item ``Equation schemes'' 
      \end{itemize} 
\item<2> Implement (as a language extension) in Agda!
      \begin{itemize}
      \item Investigate interactions with other type system features (e.g. 
            global |REWRITE| rules\footcite{cockx2020type} or
            observational\footcite{pujet2022observational}/cubical
            \footcite{cohen2016cubical} equality)
      \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}
  \centering \Large
  \emph{Thank You!}
\end{frame}

% I think putting this at the very end (after conclusion slide) and switching
% to it if someone asks would be neat
\begin{frame}
\frametitle{Related Work}

\begin{itemize}
\item |with|-abstractions/|rewrite|/pattern-matching lambdas 
      \footcite{mcbride2004view}
\item Tactics \footcite{selsam2016congruence}
\item Global |REWRITE| rules \footcite{cockx2020type}
\item ``Controlling computation in type theory, locally''
      \footcite{winterhalter2025controlling}
\item Strict η for coproducts \footcite{maillard2024splitting}
\item Extension Types \footcite{riehl2017synthetic}
\item Coq Modulo Theory (CoqMT) \footcite{strub2010modulo}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Losing Congruence of Conversion}

\alt<3>{Easily circumvented in practice!\\
The programmer can just repeat the same case split.}
{The same phenomenon occurs in Agda:\\
\phantom{The programmer can just repeat the same case split.}}

%if False
\begin{code}
not₁  : Bool → Bool
not₂  : Bool → Bool

variable
  b : Bool
\end{code}
%endif
\begin{minipage}{0.5\textwidth}\alt<3>{
\begin{spec}
not-eq : not₁ b ≡ not₂ b
not-eq {b = true}   = refl
not-eq {b = false}  = refl
\end{spec}}
{\begin{spec}
not-eq : not₁ b ≡ not₂ b
not-eq = refl 
⟨phantom⟩
\end{spec}} 
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{code}
not₁ = λ where  true   → false
                false  → true
not₂ = λ where  true   → false 
                false  → true
\end{code}
\end{minipage}

\uncover<2>{\color{BrickRed}
\begin{spec}
...:307.7-11: error: [UnequalTerms]
(λ { true → false ; false → true }) b !=
(λ { true → false ; false → true }) b of type Bool
Because they are distinct extended lambdas: one is defined at
   ...:298.8-299.30
and the other at
   ...:300.8-301.30,
so they have different internal representations.
when checking that the expression refl has type not₁ b ≡ not₂ b
\end{spec}
\color{Black}}
\end{frame}

\begin{frame}[allowframebreaks]
\frametitle{Bibliography}
\printbibliography
\end{frame}

\end{document}

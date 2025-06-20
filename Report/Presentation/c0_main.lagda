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


\documentclass{beamer}


\usepackage[style=authoryear,backend=biber]{biblatex}
\addbibresource{main.bib}

\usepackage{xpatch}
% TODO: I would like to also put the year in parens, but this is tricky
% There doesn't appear to be a way to just overwrite a bibmacro completely
\xapptobibmacro{cite}{\setunit{\nametitledelim}\printfield[emph]{title}}{}{}
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
	% I also want dois!
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
\newcommand{\SCBool}{$\textsf{SC}^\textsc{Bool}$\xspace}
\newcommand{\SCDef}{$\textsf{SC}^\textsc{Def}$\xspace}

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
\frametitle{Manual Equational Reasoning in Proof Assistants}

\centering \Large
\emph{Demo...}
%if False
\begin{code}
Bool-split : ∀ b → (b ≡ true → A) → (b ≡ false → A) → A

f3 : ∀ (f : Bool → Bool) → f true ≡ f (f (f true)) 
f3 f =  Bool-split (f true) 
        -- |f true ≡ true|
        (λ p →  f true
                ≡⟨ cong f (sym p) ⟩≡
                f (f true)
                ≡⟨ cong (λ □ → f (f □)) (sym p) ⟩≡
                f (f (f true)) ∎)
        -- |f true ≡ false|
        (λ p →  Bool-split (f false)
          -- |f false ≡ true|
          (λ q →  f true
                  ≡⟨ cong f (sym q) ⟩≡
                  f (f false)
                  ≡⟨ cong (λ □ → f (f □)) (sym p) ⟩≡ 
                  f (f (f true)) ∎)
          -- |f false ≡ false|
          (λ q →  f true
                  ≡⟨ p ⟩≡ 
                  false
                  ≡⟨ sym q ⟩≡ 
                  f false
                  ≡⟨ cong f (sym q) ⟩≡ 
                  f (f false)
                  ≡⟨ cong (λ □ → f (f □)) (sym p) ⟩≡ 
                  f (f (f true)) ∎))
\end{code}
%endif
\end{frame}

\begin{frame}
\frametitle{``Transport Hell''}

\begin{itemize}
\item<1-3> \emph{Indexed datatypes} often require equational reasoning 
      mutual with the implementation of operations (\emph{transport}).
\item<2-3> |Fin n|, |Vec A n|, |Tm Γ A| etc... 
\item<3> When proving laws about these operations, we have to account for
      these transports, using painful lemmas like \footcite{2024propprop}:
      \begin{code}
subst-application  : ∀  (B : A → Set) {C : A → Set}
                        {y} (g : ∀ x → B x → C x) 
                        (p : x₁ ≡ x₂) 
                   →  subst C p (g x₁ y) 
                   ≡  g x₂ (subst B p y)
      \end{code}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Local Equality Reflection and ``Smart Case''}
\begin{itemize}
\item<1-4> \textbf{Idea:} Extend contexts with equational assumptions.
\item<2-4> Reflecting arbitrary propositional equations is very powerful,
      but breaks decidability of typechecking.
      \[
      \frac{\begin{matrix}
      |Γ : Ctx|,\quad |A B : Ty Γ|,\quad |t₁ t₂ : Tm Γ A|\\
      |p : Tm Γ (t₁ ≡' t₂)|\\
      |u : Tm (Γ ▷ t₁ ~ t₂) (B [ wkeq ]Ty)|
      \end{matrix}}
      {|reflect p in' u : Tm Γ B|}\]
\item<3-4> Need to restrict equations somehow...
\item<4> \textbf{Starting Point:} Equations arising from (Boolean) case splits 
      \footcite{altenkirch2011case}
      \begin{itemize}
      \item The scrutinee and pattern are convertible in each branch.
      \end{itemize}  
      \[
      \frac{\begin{matrix}
      |Γ : Ctx|,\quad |t : Tm Γ 𝔹|,\quad |A : Ty Γ|\\
      |u : Tm (Γ ▷ t ~ TT) (A [ wkeq ]Ty)|\\
      |v : Tm (Γ ▷ t ~ FF) (A [ wkeq ]Ty)|
      \end{matrix}}
      {|if t then u else v : Tm Γ A|}\]
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{A Substitution Calculus}
\begin{itemize}
\item<1-3> Mapping from the empty context is trivial.
      \[\frac{}
      {|ε : Tms Δ •|}\]   
\item<2-3> To map from a context extended with a variable, 
      we need to provide a substitute term.
      \[\frac{|δ : Tms Δ Γ|,\quad |t : Tm Δ (A [ δ ]Ty)|}
      {|δ , t : Tms Δ (Γ ▷ A)|}\]
\item<3> To map from a context extended with an equation, we need to provide
      substitute \emph{evidence of convertibility}.
      \[\frac{|δ : Tms Δ Γ|,\quad |p : t₁ [ δ ] ~ t₂ [ δ ]|}
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
      quotation.\\|t ~ u → norm t ≡ norm u|
\item<4> \textbf{Completeness:} Equality 
      of normal forms implies convertibility
      of original terms (conservative).\\
      |norm t ≡ norm u → t ~ u|
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Completion}
\begin{itemize}
\item<1-4> Inconsistent contexts are dangerous!\\In the context 
      |Γ = (b ∶ 𝔹) , b ~ TT , b ~ FF|,
      all types are convertible (and looping terms can be defined).
      \begin{spec}
    A
==  IF TT A B
==  IF FF A B
==  B
      \end{spec}
\item<2-4> Deciding context inconsistency is non-trivial! 
      \begin{itemize}
      \item LHSs might be reducible: |(ƛ x. x) b ~ TT , b ~ FF|
      \item LHSs might overlap:\hspace{18.5pt} |not b ~ TT , b ~ TT| 
      \end{itemize}  
\item<3-4> The appropriate technique here is 
      \emph{completion}\footcite{baader1998term}. 
      \begin{itemize}
      \item Aims to transform a set
            of equations into a \emph{confluent} 
            \emph{term rewriting system} (TRS).
      \end{itemize}
\item<4> Needs a well-founded order... 
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Normalisation is Hard}
\begin{itemize}
\item<1-3> Evaluation must recurse into the branches of \SIF.
      \begin{itemize}
      \item Need to interleave evaluation and completion.
      \item Normal forms (also values) are not stable under extending the 
            context with equations.
      \end{itemize}
\item<2-3> \textbf{Idea:} Avoid completion by enforcing that LHSs are irreducible
      and disjoint (syntactic restriction).
      \begin{itemize}
      \item Unstable under substitution!\\
            |Γ = x ∶ 𝔹 , y ∶ 𝔹 , x ~ TT , y ~ FF|
      \item So, incompatible with most existing proof assistants (β-conversion).
      \end{itemize}
\item<3> Stability-under-substitution also rules out a lot of more interesting
      equations (beyond Booleans).
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Elaborating Case Splits to Top-Level Definitions}

Already implemented in Agda\footcite{agda2024with, agda2024lambda}

%if False
\begin{code}
data Cmp : Set where
  ge eq le : Cmp
_<_ : ℕ → ℕ → Bool
_>_ : ℕ → ℕ → Bool
\end{code}
%endif

\begin{minipage}{0.5\textwidth}
\begin{code}
cmp : ℕ → ℕ → Cmp
cmp n m  with n > m
cmp n m  | true   = ge
cmp n m  | false  with n < m
cmp n m  | false  | true   = le
cmp n m  | false  | false  = eq
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{spec}
data Cmp : Set where
  ge  : Cmp
  eq  : Cmp
  le  : Cmp
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
cmp-aux₂ n m true   = le
cmp-aux₂ n m false  = eq
\end{code}}
\vspace{-5ex}
\uncover<3-4>{
\begin{code}
cmp-aux₁ n m true   = ge
cmp-aux₁ n m false  = cmp-aux₂ n m (n < m)
\end{code}}
\vspace{-5ex}
\uncover<2-4>{\begin{code}
cmp-elab n m = cmp-aux₁ n m (n > m)
\end{code}}
\end{frame}

\begin{frame}
\frametitle{Elaborating Case Splits to Top-Level Definitions}

% TODO: Is a good idea to use different syntax for SCBool/SCDef??
\begin{spec}
f3 ∶ ∀ (f : Bool → Bool) → f true ≡ f (f (f false))
f3 f = if (f true) then refl else (if (f false) then refl else refl)
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
\frametitle{Elaborating Case Splits to Top-Level Definitions}

Two new ingredients:
\begin{itemize}
\item<2-4> Parameter lists (\emph{telescopes}) of definitions now 
      include convertibility constraints.
  \begin{itemize}
  \item (Almost) free via the substitution calculus (telescopes are
        contexts)!
  \end{itemize}  
\item<3-4> Definitions block on neutrals, and reflect appropriate equations. 
\end{itemize}

\uncover<3-4>{
\alt<4>{
\[\dfrac{\begin{matrix}
|Ξ : Sig|\quad |Γ : Ctx Ξ|\quad |A : Ty Γ|\quad |t : Tm Γ 𝔹|\\
|u : Tm (Γ ▷ t ~ TT)   (A [ wkeq ]Ty)|\\
|v : Tm (Γ ▷ t ~ FF)  (A [ wkeq ]Ty)|
\end{matrix}}
{|(Ξ ▷ Γ ⇒ A if t then u else v) : Sig|}\]}{
\[\dfrac{\begin{matrix}
|Ξ : Sig|\quad |Γ : Ctx Ξ|\quad |A B : Ty Γ|\\
|t₁ t₂ : Tm Γ B|\quad |p : Tm Γ (t₁ ≡' t₂)|\\
|u : Tm (Γ ▷ t₁ ~ t₂) (A [ wkeq ]Ty)|
\end{matrix}}
{|(Ξ ▷ Γ ⇒ A reflects p in' u) : Sig|}\]}}
\end{frame}

\begin{frame}
\frametitle{Have We Lost Anything?}

Congruence of conversion! Sort of...

\begin{itemize}
\item<2-5> Distinct case splits are elaborated to different top-level auxiliary 
definitions.
\item<3-5> Definitions only reduce after the new equation holds ``on-the-nose''.
\item<4-5> So stuck calls to distinct definitions are never convertible (even if
      the bodies are).
\item<5> Convertibility of \emph{core terms} is still congruent though!
\end{itemize}

\[\dfrac{
|f₁ ~DVar f₂|\quad |δ₁ ~Tms δ₂|}
{|call f₁ δ₁ ~Tm call f₂ δ₂|}\] 
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

\begin{frame}
\frametitle{Normalisation is Easy(er)!}

\begin{itemize}
\item<1-4> Evaluation can now be defined w.r.t. a single completed TRS.
\item<2-4> Only recurses into bodies of definitions after their blocking equation 
      holds
      ``on-the-nose'' in the calling context.
\item<3-4> Unquoting looks up neutral terms in the TRS.
\item<4> We still need to obtain the completed TRS in the first place...
      \begin{itemize}
      \item But, we can now restrict equations however we like!
      \item One possible strategy: require that LHSs are disjoint
            after normalisation.
      \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Future Work}
\begin{itemize}
\item<1-4> Support a wider class of equations
      \begin{itemize}
      \item Neutral RHSs and neutral-typed
      \item Inductive types (occurs check!)
      \item Non-disjoint LHSs (via completion - would need to find a 
            well-founded order)
      \item ``Equation schemes'' 
      \end{itemize} 
\item<2-4> Investigate interactions with other type system features (e.g. global
      |REWRITE| rules\footcite{cockx2020type} or
      observational\footcite{pujet2022observational}/cubical
      \footcite{cohen2016cubical} equality)
\item<3-4> Finish mechanised Agda proof (naturality conditions, setoid fibration
      cases, generating TRSs)
\item<4> Implement (as a language extension) in Agda!
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

\begin{frame}[allowframebreaks]
\frametitle{Bibliography}
\printbibliography
\end{frame}

\end{document}

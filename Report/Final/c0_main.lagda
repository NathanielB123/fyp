%if False
\begin{code}
module Report.Interim.c0_main where
\end{code}
%endif

% \documentclass[12pt,twoside]{report}
\documentclass[
    a4paper, % Page size
    fontsize=9.5pt, % Base font size
    twoside=false, % Use different layouts for even and odd pages (in particular, if twoside=true, the margin column will be always on the outside)
	%open=any, % If twoside=true, uncomment this to force new chapters to start on any page, not only on right (odd) pages
	%chapterentrydots=true, % Uncomment to output dots from the chapter name to the page number in the table of contents
	numbers=noenddot, % Comment to output dots after chapter numbers; the most common values for this option are: enddot, noenddot and auto (see the KOMAScript documentation for an in-depth explanation)
	fontmethod=tex, % Can also use "modern" with XeLaTeX or LuaTex; "tex" is the default for PdfLaTex, and "modern" is the default for those two.
]{kaobook}

% some definitions for the title page
\newcommand{\reporttitle}{Local Rewriting in Dependent Type Theory}
\newcommand{\reportauthor}{Nathaniel Burke}
\newcommand{\supervisor}{Dr. Steffen van Bakel}
\newcommand{\secondmarker}{Dr. Herbert Wiklicky}
\newcommand{\reporttype}{MEng Individual Project}
\newcommand{\degreetype}{MEng Computing} 

% load some definitions and default packages
\input{includes}

% 1.5 Column formatting
% \usepackage[a4paper,hmargin=2.8cm,vmargin=2.0cm,includeheadfoot]{geometry}

% load some macros
\input{notation}

\input{utilities/kaoextensions}

%include config.lagda

%include lhs2TeX.fmt
%%include polycode.fmt
%include agda_tweaked.fmt
%include lib.fmt

% load title page

\begin{document}

\pagelayout{wide}

\input{titlepage}

% page numbering etc.
\pagenumbering{roman}
\clearpage{\pagestyle{empty}\cleardoublepage}
\setcounter{page}{1}
%\pagestyle{fancy}

% Curry-Howard - Proof
\newcommand{\curry}[1]{\textit{\textcolor{Purple}{#1}}}
% Curry-Howard - Programming Language
\newcommand{\howard}[1]{\textit{\textcolor{Blue}{#1}}}

\newcommand{\smart}{\textsf{\textbf{smart}}\xspace}
\newcommand{\SC}{\textsf{\textbf{smart case}}\xspace}
\newcommand{\SIF}{\textsf{\textbf{smart if}}\xspace}
\newcommand{\SCBool}{$\textsf{SC}^\textsc{Bool}$\xspace}
\newcommand{\SCDef}{$\textsf{SC}^\textsc{Def}$\xspace}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{abstract}
Type theory provides a foundation for mechanised mathematics
and cutting-edge programming languages. Unfortunately,
to avoid ambiguity and retain decidable typechecking, 
many computer implementations
support only a primitive notion of equality, forcing tedious manual
work onto the user.
For example, users of proof assistants often resort to doing equational 
reasoning ``by hand'', not
only specifying which equational lemmas a result relies on, but also
exactly how and where to apply them.

With the aim of resolving this tedium, 
this report studies type theories with a built-in notion of
local equational assumptions. 
When designing these, a balance must be struck
between automation, predictability and decidability. Ultimately, we strike
such a balance, proving normalisation, and consequently, decidability of
typechecking for a language that we name \SCDef. We argue this language could
serve as a basis for future proof assistant development.
\end{abstract}

\cleardoublepage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\vspace*{\fill}
\small
\begin{center}
\makeatletter
{\bfseries Acknowledgements\vspace{-.5em}\vspace{\z@@}}%
\makeatother
\end{center}
\begin{quotation}
TODO
% I would like to thank:
% \begin{itemize}
%   \item Steffen van Bakel, for agreeing to supervise this project and trying
%         his best to warn me about leaving the report-writing until the last
%         minute.
%   \item David Davies, for giving fantastically-detailed feedback on drafts
%         of this report.
%         I can only apologise for not finding the time to act on all of it.
%   \item Thorsten Altenkirch and Philip Wadler, for giving me a massive
%         confidence boost by inviting me to collaborate
%         on ``Substitution Without Copy and Paste'' after I merely answered
%         a couple questions on the Agda Zulip. 
%   \item Honestly, pretty-much the whole type theory community, for 
%         being so open to sharing work in progress and answering questions
%         across the Zulips, Discords, Mastodon, StackExchange, mailing lists 
%         etc.
%         Some special shout-outs go to Simon Peyton Jones, András Kovács, 
%         Conor McBride and Amélia Liao for creating some phenomenal learning
%         resources. I also should thank Anja Petković Komel, Loïc Pujet
%         and Théo Winterhalter for inspiring me to copy their use of the 
%         |kaobook| LaTeX template. This report would look quite different if 
%         not for you!
%   \item A few more individuals from the type theory community,
%         for answering some of my questions in ways that were directly related 
%         to this project.
%         That includes Guillaume Allais, who taught me the 
%         ``don't mash the potato'' principle, Reed Mullanix, who suggested I
%         look into extension types and Raphaël Bocquet, who resolved my 
%         confusions with stabilised neutrals.
%   \item My friends, for putting up with my constant rambling about
%         dependent types for the past few years.
%         I think Aaron, Daniel, Iurii, Jacob, Jyry, Sophia and Robin probably 
%         faced the brunt of it. I also want to especially
%         thank Alona; our late-night conversations about PL design during 
%         2nd and 3rd year are a huge part of why I fell in love with this field.
%   \item My family, for not only also having to put up with my type theory
%         obsession, but also immediately supporting my pivot in future plans
%         towards academia. Those plans are 
%         admittedly looking a little shaky right now,
%         but I extremely grateful that I can count on your encouragement
%         regardless.
% \end{itemize}
\end{quotation}
\vspace*{\fill}

\clearpage{\pagestyle{empty}\cleardoublepage}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%--- table of contents
% \fancyhead[RE,LO]{\sffamily {Table of Contents}}
\tableofcontents 

\clearpage{\pagestyle{empty}\cleardoublepage}
\pagenumbering{arabic}
\setcounter{page}{1}
% \fancyhead[LE,RO]{\slshape \rightmark}
% \fancyhead[LO,RE]{\slshape \leftmark}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\mainmatter % Denotes the start of the main document content, resets page numbering and uses arabic numbers
\setchapterstyle{kao} % Choose the default chapter heading style
\pagelayout{margin}

% From https://tex.stackexchange.com/questions/325297/how-to-scale-a-tikzcd-diagram
\tikzcdset{scale cd/.style={every label/.append style={scale=#1},
    cells={nodes={scale=#1}}}}

\tikzcdset{scaleedge cd/.style={every label/.append style={scale=#1}}}
\tikzcdset{scalecell cd/.style={cells={nodes={scale=#1}}}}

\newcommand{\nocodeindent}{\setlength\mathindent{0em}}
\newcommand{\resetcodeindent}{\setlength\mathindent{1em}}


\resetcodeindent

%%include c0-1_test.lagda

%include c1-1_introduction.lagda
%include c2-1_background.lagda
%include c2-2_background.lagda
%include c2-3_background.lagda
%include c2-4_background.lagda
%include c2-5_background.lagda
%include c2-6_background.lagda
%include c2-7_background.lagda
%include c3-1_related.lagda
%include c4-1_booleq.lagda
%include c4-2_booleq.lagda
%include c4-3_booleq.lagda
%include c4-4_booleq.lagda
%include c5-1_scbool.lagda
%include c6-1_scdef.lagda
%include c6-2_scdef.lagda


%% bibliography
% \bibliographystyle{apa}
\setchapterstyle{plain} % Output plain chapters from this point onwards
\pagelayout{wide}
\sloppy
\printbibliography[heading=bibintoc, title=Bibliography]


\end{document}

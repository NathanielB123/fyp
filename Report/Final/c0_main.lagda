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
\newcommand{\reporttype}{MEng Individual Project (Interim Report)}
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

% \input{titlepage}

% page numbering etc.
\pagenumbering{roman}
\clearpage{\pagestyle{empty}\cleardoublepage}
\setcounter{page}{1}
% \pagestyle{fancy}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \begin{abstract}
% Your abstract.
% \end{abstract}

% \cleardoublepage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \section*{Acknowledgments}
% Comment this out if not needed.

% \clearpage{\pagestyle{empty}\cleardoublepage}

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

% Curry-Howard - Proof
\newcommand{\curry}[1]{\textit{\textcolor{Purple}{#1}}}
% Curry-Howard - Programming Language
\newcommand{\howard}[1]{\textit{\textcolor{Blue}{#1}}}

\newcommand{\smart}{\textsf{\textbf{smart}}\xspace}
\newcommand{\SC}{\textsf{\textbf{smart case}}\xspace}
\newcommand{\SIF}{\textsf{\textbf{smart if}}\xspace}
\newcommand{\SCBool}{$\textsf{SC}^\textsc{Bool}$\xspace}
\newcommand{\SCDef}{$\textsf{SC}^\textsc{Def}$\xspace}

\newcommand{\nocodeindent}{\setlength\mathindent{0em}}
\newcommand{\resetcodeindent}{\setlength\mathindent{1em}}


\resetcodeindent

%%include c0-1_test.lagda

%include c1-1_introduction.lagda
%%include c2-1_background.lagda
%%include c2-2_background.lagda
%%include c2-3_background.lagda
%%include c2-4_background.lagda
%%include c2-5_background.lagda
%%include c2-6_background.lagda
%%include c2-7_background.lagda
%%include c3-1_related.lagda
%%include c4-1_booleq.lagda
%%include c4-2_booleq.lagda
%%include c4-3_booleq.lagda
%%include c5-1_scbool.lagda
%%include c6-1_scdef.lagda
%%include c6-2_scdef.lagda


%% bibliography
% \bibliographystyle{apa}
\setchapterstyle{plain} % Output plain chapters from this point onwards
\pagelayout{wide}
\sloppy
\printbibliography[heading=bibintoc, title=Bibliography]


\end{document}

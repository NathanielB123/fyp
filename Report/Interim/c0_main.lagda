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

\input{titlepage}

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

%include c1_introduction.lagda
%include c2_background.lagda
%%include c3_simplytyped.lagda
%%include c4_dependentlytyped.lagda
%include c5_plan.lagda


%% bibliography
% \bibliographystyle{apa}
\setchapterstyle{plain} % Output plain chapters from this point onwards
\pagelayout{wide}
\printbibliography[heading=bibintoc, title=Bibliography]


\end{document}

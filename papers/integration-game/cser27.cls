\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{cser27}[2027/04/11 CSER 2027 Conference Paper Class]

% Base class: article 10pt letterpaper
\PassOptionsToClass{10pt,letterpaper}{article}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax
\LoadClass{article}

% Geometry: 1-inch margins
\RequirePackage[margin=1in]{geometry}

% Font: Helvetica sans-serif as document default
\RequirePackage{helvet}
\renewcommand{\familydefault}{\sfdefault}

% Core Packages
\RequirePackage{graphicx}
\RequirePackage{booktabs}
\RequirePackage{titlesec}
\RequirePackage{authblk}
\RequirePackage{caption}
\RequirePackage{indentfirst}
\RequirePackage{url}
\RequirePackage[hidelinks]{hyperref}
\RequirePackage{float}
\RequirePackage{amsmath}
\RequirePackage{amsfonts}
\RequirePackage{amssymb}
\RequirePackage{mathtools}
\RequirePackage{framed}
\RequirePackage[style=numeric-comp, sorting=none, backend=biber]{biblatex}

% BibLaTeX CSER style customization
\DeclareFieldFormat{labelnumberwidth}{#1\adddot}
\renewcommand*{\bibfont}{\footnotesize}
\DeclareFieldFormat{titlecase}{\MakeSentenceCase*{#1}}

% Section Heading Formatting: Bold, 10pt, Numbered
\titleformat{\section}
  {\normalfont\bfseries\normalsize}
  {\thesection.}
  {0.5em}
  {}

\titleformat{\subsection}
  {\normalfont\bfseries\normalsize}
  {\thesubsection}
  {0.5em}
  {}

% Caption Formatting
\captionsetup[table]{position=bottom, justification=centering, labelsep=period, font={footnotesize,it}}
\captionsetup[figure]{position=bottom, font=footnotesize, justification=centering, labelsep=period, name={Fig.}}

% Paragraph spacing: no paragraph skip, use indentation
\setlength{\parskip}{0pt}

% Metadata and Configuration Macros
\newcommand{\cserlogo}[1]{\def\@cserlogo{#1}}
\cserlogo{cser27-logo.png}

\newcommand{\conferencename}[1]{\def\@conferencename{#1}}
\conferencename{24\textsuperscript{th} Annual Conference on Systems Engineering Research}

\newcommand{\conferencetheme}[1]{\def\@conferencetheme{#1}}
\conferencetheme{Architecting Socio-technical Systems for a Connected and Contested World}

\newcommand{\conferencelocation}[1]{\def\@conferencelocation{#1}}
\conferencelocation{Huntsville, AL, USA April 11--14, 2027}

\newcommand{\conferenceeditors}[1]{\def\@conferenceeditors{#1}}
\conferenceeditors{}

\newcommand{\conferenceeditoraffil}[1]{\def\@conferenceeditoraffil{#1}}
\conferenceeditoraffil{}

% Author & Affiliation font settings for authblk
\renewcommand\Authfont{\fontsize{10}{12}\selectfont\itshape}
\renewcommand\Affilfont{\fontsize{9}{11}\selectfont}
\setlength{\affilsep}{0.2cm}

% Header block and Title formatting
\renewcommand{\maketitle}{%
  \begingroup
  \global\@topnum\z@
  \noindent
  \begin{tabular}{@{} p{0.30\textwidth} @{\hspace{0.02\textwidth}} p{0.68\textwidth} @{}}
    \begin{minipage}[c]{\linewidth}
      \IfFileExists{\@cserlogo}{%
        \includegraphics[width=\linewidth]{\@cserlogo}%
      }{%
        \fbox{\parbox[c][0.7in][c]{\linewidth}{\centering [Logo Missing]}}%
      }
    \end{minipage}
    &
    \begin{minipage}[c]{\linewidth}
      \raggedright
      \fontsize{12}{14}\selectfont\textbf{\textit{\@conferencename}}\\
      \vspace{0.3em}
      \fontsize{11}{13}\selectfont\textit{\@conferencetheme}
    \end{minipage}
  \end{tabular}

  \vspace{0.5cm}

  % Editors and Location Block
  \begin{center}
    \ifx\@conferenceeditors\@empty
      {\fontsize{10}{12}\selectfont\textbf{\textit{\@conferencelocation}}}
    \else
      {\fontsize{10}{12}\selectfont\bfseries\itshape
      Editors: \@conferenceeditors} \\
      \ifx\@conferenceeditoraffil\@empty\else
        \vspace{0.2cm}
        {\fontsize{9}{11}\selectfont\itshape \@conferenceeditoraffil} \\
      \fi
      \vspace{0.3cm}
      {\fontsize{10}{12}\selectfont\textbf{\textit{\@conferencelocation}}}
    \fi
  \end{center}

  \vspace{0.5cm}

  % Title, Authors, and Affiliations
  \begin{center}
    {\fontsize{14}{17}\selectfont\textbf{\@title}\par}
    \vspace{0.5cm}
    \@author\par
  \end{center}
  \vspace{0.5cm}
  \endgroup
}

% Abstract environment
\renewenvironment{abstract}{%
  \begin{center}
    {\fontsize{9}{11}\selectfont\textbf{Abstract}\par}
  \end{center}
  \begingroup
  \fontsize{9}{11}\selectfont\noindent\ignorespaces
}{%
  \par
  \endgroup
  \vspace{0.5cm}
}

% Keywords command
\newcommand{\keywords}[1]{%
  {\fontsize{8}{10}\selectfont\bfseries\itshape\noindent Keywords: #1}\par\vspace{0.5cm}
}

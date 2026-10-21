%% syseng.cls
%% Reverse-engineered LaTeX2e document class for the Wiley "Systems Engineering"
%% (INCOSE) modern journal layout (2025/2026 design).
%% Optimized for Regular Articles based on forensic PDF analysis.
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{syseng}[2026/10/20 v2.1 Modern Wiley Systems Engineering Journal Class]

%% Article type options
\newcommand{\@articletype}{REGULAR ARTICLE}
\DeclareOption{regular}{\renewcommand{\@articletype}{REGULAR ARTICLE}}
\DeclareOption{review}{\renewcommand{\@articletype}{REVIEW ARTICLE}}
\DeclareOption{communication}{\renewcommand{\@articletype}{SHORT COMMUNICATION}}
\DeclareOption{editorial}{\renewcommand{\@articletype}{EDITORIAL}}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax

\LoadClass[10pt,twocolumn,twoside]{article}

%% Required packages
\RequirePackage[T1]{fontenc}
\RequirePackage[utf8]{inputenc}
\RequirePackage{stix2}
\RequirePackage{amsmath}
\RequirePackage{graphicx}
\RequirePackage{xcolor}
\RequirePackage{fancyhdr}
\RequirePackage{lastpage}
\RequirePackage{titlesec}
\RequirePackage{caption}
\RequirePackage{booktabs}
\RequirePackage{array}
\RequirePackage{enumitem}
\RequirePackage{cite}
\RequirePackage{url}

%% Exact Colors from Reference PDF trace
%% Gray boxes: DeviceGray 0.9 = #E6E6E6
%% Hyperlinks: DeviceRGB 0 0 1 = #0000FF
\definecolor{sysenggray}{gray}{0.90}
\definecolor{sysengblue}{rgb}{0,0,1}
\definecolor{orcidgreen}{cmyk}{0.37855,0.038148,1,0}

\RequirePackage[
  colorlinks=true,
  linkcolor=sysengblue,
  citecolor=sysengblue,
  urlcolor=sysengblue
]{hyperref}
\urlstyle{same}

%% Exact Page Geometry from Reference PDFs (612.284bp x 799.37bp = 216mm x 282mm)
%% Left column: 53.61bp .. 300.98bp (247.37bp)
%% Column sep:  13.41bp
%% Right column: 314.39bp .. 561.76bp (247.37bp)
%% Total textwidth: 508.15bp
\RequirePackage[
  paperwidth=612.284bp,
  paperheight=799.37bp,
  left=53.61bp,
  textwidth=508.15bp,
  top=38.32bp,
  bottom=60.75bp,
  columnsep=13.41bp,
  headheight=0bp,
  headsep=0bp,
  footskip=22.5bp
]{geometry}

%% Constant vertical spacing (no column-stretching gaps)
\raggedbottom

%% Body Font Size (9pt on 11.5pt leading) & Flush-Left Paragraphs with 1-Line Parskip
\renewcommand{\normalsize}{%
  \@setfontsize\normalsize{9pt}{11.5pt}%
  \abovedisplayskip 8bp \@plus2bp \@minus2bp
  \abovedisplayshortskip \z@ \@plus2bp
  \belowdisplayshortskip 4bp \@plus2bp \@minus2bp
  \belowdisplayskip \abovedisplayskip
  \let\@listi\@listI
}
\normalsize
\setlength{\parindent}{0pt}
\setlength{\parskip}{11.5pt}

%% Booktabs exact rule widths from Reference PDF trace
\setlength{\heavyrulewidth}{0.75bp}
\setlength{\lightrulewidth}{0.40bp}

%% Metadata macros (use \let...\@empty so \ifx...\@empty tests work reliably)
\newcommand{\@journalname}{Systems Engineering}
\newcommand{\journalname}[1]{\renewcommand{\@journalname}{#1}}

\newcommand{\@pubyear}{\the\year}
\newcommand{\pubyear}[1]{\renewcommand{\@pubyear}{#1}}

\newcommand{\@volume}{0}
\newcommand{\volume}[1]{\renewcommand{\@volume}{#1}}

\newcommand{\@doi}{10.1002/sys.00000}
\newcommand{\doi}[1]{\renewcommand{\@doi}{#1}}

\newcommand{\@received}{1 January 2026}
\newcommand{\received}[1]{\renewcommand{\@received}{#1}}

\newcommand{\@revised}{1 March 2026}
\newcommand{\revised}[1]{\renewcommand{\@revised}{#1}}

\newcommand{\@accepted}{1 April 2026}
\newcommand{\accepted}[1]{\renewcommand{\@accepted}{#1}}

\newcommand{\@correspondence}{Author Name (\href{mailto:author@institution.edu}{author@institution.edu})}
\newcommand{\correspondence}[1]{\renewcommand{\@correspondence}{#1}}

\let\@keywords\@empty
\newcommand{\keywords}[1]{\def\@keywords{#1}}

\let\@funding\@empty
\newcommand{\funding}[1]{\def\@funding{#1}}

\let\@affiliations\@empty
\newcommand{\affiliations}[1]{\def\@affiliations{#1}}

\let\@abstract\@empty
\renewcommand{\abstract}[1]{\def\@abstract{#1}}

\newcommand{\@copyrightline}{%
  All rights reserved, including rights for text and data mining and training of artificial intelligence technologies or similar technologies.\par
  \copyright\ \@pubyear\ Wiley Periodicals LLC.%
}
\newcommand{\copyrightline}[1]{\renewcommand{\@copyrightline}{#1}}

%% Helper macros for authors, affiliations, ORCID, and keywords
%% Vertical rules match exact vector stroke paths in Reference PDFs
\newcommand{\affilmark}[1]{\textsuperscript{\fontsize{6}{6}\selectfont\textcolor{sysengblue}{#1}}}
\newcommand{\affilnum}[1]{\textsuperscript{\fontsize{5.25}{5.25}\selectfont #1}}
\newcommand{\authorsep}{\hspace{5.5bp}\rule[-1bp]{0.5bp}{7bp}\hspace{5.5bp}}
\newcommand{\affilsep}{\hspace{3.5bp}\rule[-0.75bp]{0.5bp}{5.5bp}\hspace{3.5bp}}
\newcommand{\datesep}{\hspace{3.5bp}\rule[-0.75bp]{0.5bp}{6bp}\hspace{3.5bp}}
\newcommand{\kwsep}{\hspace{3.5bp}\rule[-0.75bp]{0.5bp}{6bp}\hspace{3.5bp}}

%% Optional vector ORCID icon matching Reference PDF
\newcommand{\orcid}[1]{%
  \hspace{2bp}\href{https://orcid.org/#1}{%
    \vbox to 7bp{\vss\hbox{%
      \setlength{\fboxsep}{1.1bp}%
      \colorbox{orcidgreen}{\fontsize{4.5}{4.5}\selectfont\textcolor{white}{\textbf{iD}}}%
    }\vss}%
  }%
}

%% Dashed horizontal rule helper for Page 1 footer (0.5bp thick, 2bp dash, 2bp gap)
\newcommand{\syseng@dashedrule}{%
  \hbox to \textwidth{%
    \leaders\hbox to 4bp{\rule{2bp}{0.5bp}\hss}\hfill\rule{2bp}{0.5bp}%
  }%
}

%% Page styles (headers and footers)
\pagestyle{fancy}
\fancyhf{}
\renewcommand{\headrulewidth}{0pt}
\renewcommand{\footrulewidth}{0pt}

%% Running footer for pages 2+ (solid 0.5bp rule on all pages + odd/even alternation)
\fancypagestyle{main}{%
  \fancyhf{}%
  \renewcommand{\headrulewidth}{0pt}%
  \renewcommand{\footrulewidth}{0pt}%
  \fancyfoot[C]{%
    \vbox to 0pt{%
      \vspace*{-14.5bp}%
      \noindent\rule{\textwidth}{0.5bp}\par
      \vspace{3.5bp}%
      \hb@xt@\textwidth{%
        \ifodd\c@page
          {\fontsize{7}{9}\selectfont\textit{\@journalname}, \@pubyear}%
          \hfill
          {\fontsize{9}{11}\selectfont\thepage\ of \pageref*{LastPage}}%
        \else
          {\fontsize{9}{11}\selectfont\thepage\ of \pageref*{LastPage}}%
          \hfill
          {\fontsize{7}{9}\selectfont\textit{\@journalname}, \@pubyear}%
        \fi
      }%
      \vss
    }%
  }%
}

%% First-page footer (dashed rule + flush-left copyright + solid 0.5bp rule + 2-line citation/DOI + 1 of N)
%% Note: Page 1 \textheight is shortened by 46bp so both columns stop above the dashed rule;
%% we restore \textheight inside the firstpage footer right as Page 1 ships out.
\fancypagestyle{firstpage}{%
  \fancyhf{}%
  \renewcommand{\headrulewidth}{0pt}%
  \renewcommand{\footrulewidth}{0pt}%
  \fancyfoot[C]{%
    \vbox to 0pt{%
      \vspace*{-13bp}%
      \parbox{\textwidth}{%
        \setlength{\parindent}{0pt}%
        \setlength{\parskip}{0pt}%
        \noindent\syseng@dashedrule\par
        \vspace{9bp}%
        {\fontsize{7}{10}\selectfont\noindent\@copyrightline\par}%
        \vspace{7.5bp}%
        \noindent\rule{\textwidth}{0.5bp}\par
        \vspace{3.5bp}%
        \hb@xt@\textwidth{%
          \vbox{\hbox{\fontsize{7}{8.4}\selectfont\textit{\@journalname}, \@pubyear; \@volume:1--\pageref*{LastPage}}%
                \vspace{1bp}%
                \hbox{\fontsize{7}{8.4}\selectfont\href{https://doi.org/\@doi}{https://doi.org/\@doi}}}%
          \hfill
          \raisebox{3bp}{\fontsize{9}{11}\selectfont 1 of \pageref*{LastPage}}%
        }%
      }%
      \vss
    }%
    \global\advance\textheight by 46bp\relax
  }%
}

\pagestyle{main}

%% Title & Masthead Block (Full-Width Spanning Both Columns on Page 1)
\renewcommand{\maketitle}{%
  %% Shorten Page 1 \textheight by 46bp before \twocolumn calculates column room
  \global\advance\textheight by -46bp\relax
  \global\@colht\textheight
  \twocolumn[{%
    \begingroup
      \setlength{\parindent}{0pt}%
      \setlength{\parskip}{0pt}%
      %% Top banner: Gray highlight box around "Systems Engineering" (12pt BoldItalic) + Vector WILEY logo
      \vspace*{2bp}%
      \noindent
      \hbox to \textwidth{%
        \setlength{\fboxsep}{0pt}%
        \colorbox{sysenggray}{%
          \rule[-5.63bp]{0pt}{16.98bp}%
          \hspace{3bp}%
          {\fontsize{12}{12}\selectfont\textbf{\textit{\@journalname}}}%
          \hspace{3bp}%
        }%
        \hfill
        \IfFileExists{wiley-logo.pdf}{%
          \raisebox{-5.2bp}{\includegraphics[width=80.30bp]{wiley-logo.pdf}}%
        }{%
          {\fontsize{13}{13}\selectfont\textbf{WILEY}}%
        }%
        \hspace*{3.5bp}%
      }\par
      \vspace{61bp}%
      %% Article Type with 4bp x 14bp vertical black bar + 10pt Bold STIXTwoText
      \noindent
      \rule[-3bp]{3.99bp}{13.95bp}\hspace{5.63bp}%
      {\fontsize{10}{12}\selectfont\textbf{\@articletype}}\par
      \vspace{27bp}%
      %% Article Title (18pt / 21pt Bold STIXTwoText)
      {\fontsize{18}{21}\selectfont\textbf{\@title}\par}%
      \vspace{10bp}%
      %% Authors (9pt / 11pt Regular STIXTwoText)
      {\fontsize{9}{11}\selectfont \@author\par}%
      \vspace{12bp}%
      %% Affiliations (7.5pt / 11.3pt Regular STIXTwoText)
      \ifx\@affiliations\@empty\else
        {\fontsize{7.5}{11.3}\selectfont \@affiliations\par}%
        \vspace{8bp}%
      \fi
      %% Correspondence (7.5pt, 16.4bp baseline-to-baseline spacing)
      {\fontsize{7.5}{10}\selectfont\textbf{Correspondence:} \@correspondence\par}%
      \vspace{6.4bp}%
      %% Dates: Received | Revised | Accepted (7.5pt)
      {\fontsize{7.5}{10}\selectfont
        \textbf{Received:} \@received \datesep
        \textbf{Revised:} \@revised \datesep
        \textbf{Accepted:} \@accepted
        \ifx\@funding\@empty\else
          \par\vspace{6.4bp}\textbf{Funding information:} \@funding
        \fi
      \par}%
      \vspace{6.4bp}%
      %% Keywords (7.5pt)
      \ifx\@keywords\@empty\else
        {\fontsize{7.5}{10}\selectfont\textbf{Keywords:} \@keywords\par}%
      \fi
      \vspace{18bp}%
      %% Abstract Gray Box (DeviceGray 0.9 = #E6E6E6, 10bp padding, 10pt Bold heading, 9pt/13pt body)
      \ifx\@abstract\@empty\else
        \setlength{\fboxsep}{10bp}%
        \noindent
        \colorbox{sysenggray}{%
          \parbox{\dimexpr\textwidth-20bp\relax}{%
            \vspace{2bp}%
            {\fontsize{10}{12}\selectfont\textbf{ABSTRACT}\par}%
            \vspace{4bp}%
            {\fontsize{9}{13}\selectfont\setlength{\parindent}{0pt}\setlength{\parskip}{6bp}\@abstract\par}%
            \vspace{2bp}%
          }%
        }\par
      \fi
      \vspace{22bp}%
    \endgroup
  }]%
  \thispagestyle{firstpage}%
}

%% Section Headings
%% Both \section and \subsection use 10pt STIXTwoText-Bold with a 1bp x 8bp vertical rule
%% and 10bp horizontal padding on each side (\thesection \hspace{10bp}\rule[-1bp]{1bp}{8bp}\hspace{10bp})
%% Note: titlesec adds \parskip (11.5pt) to both beforeskip and afterskip, so we set afterskip=1bp.
\titleformat{\section}
  {\fontsize{10}{12}\selectfont\bfseries\raggedright}
  {\thesection\hspace{10bp}\rule[-1bp]{1bp}{8bp}\hspace{10bp}}
  {0pt}
  {}
\titlespacing*{\section}{0pt}{15bp}{1bp}

\titleformat{\subsection}
  {\fontsize{10}{12}\selectfont\bfseries\raggedright}
  {\thesubsection\hspace{10bp}\rule[-1bp]{1bp}{8bp}\hspace{10bp}}
  {0pt}
  {}
\titlespacing*{\subsection}{0pt}{11bp}{1bp}

\titleformat{\subsubsection}
  {\fontsize{9}{11.5}\selectfont\bfseries\raggedright}
  {\thesubsubsection\hspace{8bp}\rule[-1bp]{0.75bp}{7.5bp}\hspace{8bp}}
  {0pt}
  {}
\titlespacing*{\subsubsection}{0pt}{8bp}{0bp}

%% Endmatter Sections (Funding, Conflicts of Interest, Data Availability Statement, etc.)
%% 8pt Bold heading + 8pt/10pt Regular body text (13.45bp baseline-to-baseline after heading)
\newcommand{\backmattersection}[2]{%
  \par\vspace{4.3bp}%
  \begingroup
    \fontsize{8}{10}\selectfont
    \setlength{\parskip}{0pt}%
    \noindent\textbf{#1}\par
    \vspace{3.45bp}%
    \noindent #2\par
  \endgroup
}
\let\endmattersection\backmattersection

%% Figure and Table Captions
%% 8pt Bold uppercase "FIGURE X" / "TABLE X" (no period) + 0.5bp x 6.5bp vertical rule + 8pt Regular text
\DeclareCaptionFont{sysengcap}{\fontsize{8}{10}\selectfont}
\DeclareCaptionLabelFormat{sysenglabel}{\textbf{\MakeUppercase{#1}\ #2}}
\DeclareCaptionLabelSeparator{sysengsep}{\hspace{5bp}\rule[-0.5bp]{0.5bp}{6.5bp}\hspace{8bp}}
\captionsetup{
  font=sysengcap,
  labelformat=sysenglabel,
  labelsep=sysengsep,
  singlelinecheck=false,
  justification=justified,
  aboveskip=6bp,
  belowskip=4bp
}
\captionsetup[table]{
  position=top,
  aboveskip=0bp,
  belowskip=5bp
}

%% Compact Lists matching 9pt/11.5pt body text
\setlist{
  font=\normalsize,
  leftmargin=12bp,
  itemsep=2bp,
  topsep=2bp,
  parsep=0pt,
  partopsep=0pt
}

%% References (8pt Bold "References" heading; 8pt/10pt flush-left numbered entries "1. " with 4bp itemsep)
\renewcommand{\@biblabel}[1]{}
\def\@bibitem#1{%
  \item
  \Hy@raisedlink{\hyper@anchorstart{cite.#1}\hyper@anchorend}%
  \if@filesw\immediate\write\@auxout{\string\bibcite{#1}{\the\value{\@listctr}}}\fi
  \the\value{\@listctr}.\space\ignorespaces
}
\renewenvironment{thebibliography}[1]{%
  \par\vspace{4.3bp}%
  \begingroup
    \fontsize{8}{10}\selectfont
    \setlength{\parskip}{0pt}%
    \noindent\textbf{\refname}\par
    \vspace{4.9bp}%
  \endgroup
  \fontsize{8}{10}\selectfont
  \setlength{\parskip}{0pt}%
  \list{}{%
    \setlength{\leftmargin}{0pt}%
    \setlength{\itemindent}{0pt}%
    \setlength{\labelwidth}{0pt}%
    \setlength{\labelsep}{0pt}%
    \setlength{\itemsep}{4bp}%
    \setlength{\parsep}{0pt}%
    \setlength{\topsep}{0pt}%
    \usecounter{enumiv}%
    \let\p@enumiv\@empty
    \renewcommand\theenumiv{\@arabic\c@enumiv}%
  }%
  \sloppy
  \clubpenalty4000
  \@clubpenalty \clubpenalty
  \widowpenalty4000%
  \sfcode`\.\@m
}{%
  \def\@noitemerr{\@latex@warning{Empty `thebibliography' environment}}%
  \endlist
}

\endinput

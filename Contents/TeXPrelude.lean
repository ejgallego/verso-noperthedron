import Verso
import VersoManual
import VersoBlueprint

open Informal

tex_prelude r#"
% KaTeX in the current harness is missing this shorthand.
\newcommand{\Q}{\mathbb{Q}}
% \newcommand{\R}{\mathbb{R}}
% \newcommand{\N}{\mathbb{N}}
\newcommand{\hull}[1]{\mathsf{Co}(#1)}
\newcommand{\PPP}{\mathbf{P}}
\newcommand{\OOO}{\mathbf{O}}
\newcommand{\PP}{\mathcal{P}}
\newcommand{\QQ}{\mathcal{Q}}
\newcommand{\id}{\mathrm{Id}}
\newcommand{\spanp}{\mathrm{span}^+}

\newcommand{\NOP}{\mathbf{NOP}}
\newcommand{\RUP}{\mathbf{RUP}}
\newcommand{\RID}{\mathbf{RID}}

\newcommand{\Circ}{\mathrm{Disc}}
\newcommand{\Sect}{\mathrm{Sect}}

\newcommand{\dd}{\mathrm{d}}

\newcommand{\thetab}{\overline{\theta}}
\newcommand{\phib}{\overline{\varphi}}
\newcommand{\alphab}{\overline{\alpha}}
\newcommand{\Mib}{\overline{M_1}}
\newcommand{\Miib}{\overline{M_2}}
\newcommand{\Xib}{\overline{X_1}}
\newcommand{\Xiib}{\overline{X_2}}

\newcommand{\ssin}{\sin_{\mathbb{Q}}}
\newcommand{\scos}{\cos_{\mathbb{Q}}}
"#

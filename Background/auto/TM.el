(TeX-add-style-hook
 "TM"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("report" "11pt")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("parskip" "parfill") ("xy" "all") ("babel" "english") ("geometry" "top=1.3in" "bottom=1.6in" "left=1.3in" "right=1.3in") ("algorithm2e" "ruled" "vlined")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "report"
    "rep11"
    "parskip"
    "graphicx"
    "amssymb"
    "amsmath"
    "mathrsfs"
    ""
    "amsthm"
    "epstopdf"
    "enumerate"
    "tikz"
    "listings"
    "color"
    "xy"
    "babel"
    "setspace"
    "soul"
    "hyperref"
    "geometry"
    "booktabs"
    "algorithm2e")
   (TeX-add-symbols
    '("edit" 1)
    "eps"
    "arraystretch")
   (LaTeX-add-labels
    "cha:do-list"
    "sec:theory"
    "subsec:rafael"
    "sec:code"
    "sec:paper"
    "cha:preliminaries"
    "sec:pAdicValuations"
    "sec:pAdicLogarithms"
    "lem: pAdicLogarithms"
    "lem:pAdicLogarithms2"
    "sec:WeilHeight"
    "sec:EllipticCurves"
    "eq:EllipticCurve"
    "sec:CubicForms"
    "sec:Lattices"
    "sec:continued-fractions"
    "th:convergentbound"
    "sec:gener-cont-fract"
    "ch:AlgorithmsForTM"
    "sec:FirstSteps"
    "eq:ThueMahler"
    "eq:ThueMahler2"
    "sec:RelevantAlgNumField"
    "eq:ThueMahler3"
    "eq:normTM"
    "eq:idealTM"
    "sec:PIRL"
    "eq:Lp"
    "eq:Mp"
    "lem:AffinePatch1"
    "lem:AffinePatch2"
    "alg:AffinePatch1"
    "lem:AffinePatch1Check"
    "alg:AffinePatch2"
    "lem:AffinePatch2Check"
    "subsec:PIRLRemarks"
    "sec:FactorizationTM"
    "eq:TMfactored"
    "subsec:FactorizationTMwithoutOK"
    "subsec:FactorizationTMwithOK"
    "subsec:SUnitEquation"
    "eq:TMprincipal"
    "eq:TMinK"
    "eq:Sunit"
    "subsec:FactorizationRemarks"
    "sec:SmallBoundForSpecialCase"
    "lem:SunitUnits"
    "lem:Delta1"
    "eq:LambdaL"
    "lem:DiscG"
    "lem:Lambda"
    "lem:specialcase"
    "sec:LatticeReduction"
    "subsec:LLL"
    "lem:LLL"
    "subsec:FinckePohst"
    "eq:ShortVector"
    "eq:CholeskyCoeffs"
    "subsec:FinckePohstRemarks"
    "eq:TransShortVector"
    "eq:TransShortVector2"
    "cha:comp-ellipt-curv"
    "sec:elliptic-curves"
    "first"
    "tab nu2"
    "tab nu3"
    "tab nup"
    "sec:cubic-forms:-main-1"
    "form0"
    "claire-bear"
    "syz"
    "resultant"
    "fisk"
    "TM-eq"
    "curvey"
    "Dee"
    "term0"
    "term1"
    "term2"
    "term3"
    "sec:remarks"
    "lumpy"
    "froggie"
    "dahlia"
    "syz2"
    "Mordell"
    "sec:algorithm"
    "sec:proof-theor-autor"
    "first2"
    "super-1"
    "super0"
    "super"
    "tab nu2 nxym"
    "tab nu3 nxym"
    "a1"
    "a2"
    "truth"
    "definite"
    "three"
    "three-2"
    "foster"
    "toothbrush"
    "flag"
    "sec:find-repr-forms"
    "sec:reducible-forms"
    "weger"
    "S-square"
    "sec:comp-forms-fixed"
    "sec:mboxgl_2m-vs-mboxsl"
    "sec:pseud-find-repr"
    "ch:EfficientTMSolver"
    "Eq:TM1"
    "eq:EfficientSunit"
    "eq:Efficientpoly"
    "eq:Efficientg"
    "sec:decomp-weil-height"
    "lem:cancellation"
    "lem:ordpz"
    "prop:heightdecomp"
    "eq:hdecomp"
    "sec:InitialHeightBounds"
    "eq:TrueSunit"
    "lem:TMinitialheight"
    "eq:Omegaprime"
    "sec:CoveringsofSigma"
    "lem:covering"
    "sec:ConstructionofEllipsoids"
    "lem:boundqf"
    "eq:wepslk"
    "eq:wgammalk"
    "lem:mepsbound"
    "subsec:ArchEllipsoid"
    "eq:alpha0eps"
    "eq:alphagamma"
    "eq:wsigma"
    "lem:archellest"
    "def:bbound"
    "def:bepsbound"
    "def:bepstarbound"
    "def:ellreal"
    "subsec:nonArchEllipsoid"
    "def:ellp"
    "sec:archsieve"
    "lem:archsieve"
    "sec:nonArchSieve"
    "sec:apply-lemma-refl-1"
    "sec:apply-lemma-refl"
    "sec:reduction-procedure"
    "Lem:19.1"
    "lem:lambdap"
    "lem:nonarch1"
    "cor:hvequiv")
   (LaTeX-add-index-entries
    "cubic forms"
    "Thue-Mahler equations"
    "covariants"
    "conductor")
   (LaTeX-add-amsthm-newtheorems
    "theorem"
    "conjecture"
    "corollary"
    "lemma"
    "properties"
    "proposition"
    "problem"
    "question"
    "Algorithm"
    "definition"
    "example"
    "remark")
   (LaTeX-add-color-definecolors
    "grau"
    "dkgreen"
    "gray"
    "mauve"))
 :latex)


$out_dir = "build";

$tex_src .= "\\input{%S}";

$bibtex_use = 2;

$pdf_mode = 1;
$pdflatex = "texfot --ignore '^Underfull' --ignore '^Overfull' --ignore '^Marginpar' pdflatex %O -interaction=nonstopmode -synctex=1 -shell-escape \"$tex_src\"";


# latexmk configuration for latex_viterbo
# Default: incremental builds into build/, override with OUTDIR env

use Cwd;
my $root = Cwd::abs_path('.');
my $out = $ENV{'OUTDIR'} // 'build';
$out_dir = "$root/$out";
$aux_dir = $out_dir;

$pdf_mode = 1;

# Engine locked to pdflatex for reproducibility and speed
$pdflatex = 'pdflatex -synctex=1 -file-line-error -interaction=nonstopmode %O %S';
$bibtex_use = 2;           # use biber if .bcf exists, else bibtex
$recorder = 1;             # helps dependency tracking
$silent = 1;               # quiet unless errors

# Clean additional artifacts
@clean_ext = ('synctex.gz');

# latexmk configuration for latex_talk_clarke_duality
# Default: incremental builds into build/, override with OUTDIR env

use Cwd;
my $root = Cwd::abs_path('.');
my $out = $ENV{'OUTDIR'} // 'build';
$out_dir = "$root/$out";
$aux_dir = $out_dir;

$pdf_mode = 1;

# Engine locked to pdflatex for reproducibility and speed
$pdflatex = 'pdflatex -synctex=1 -file-line-error -interaction=nonstopmode %O %S';
$recorder = 1;
$silent = 1;

@clean_ext = ('synctex.gz');


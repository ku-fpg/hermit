# hacky tests
#
# Assuming that the HERMIT package has already been install
#

sub compileAndRun {
	my ($style,$mod) = @_;
	print "compiling $mod, using ($style)\n";
	$str = "ghc-7.4.1 ${mod}.hs " .
               "    -fforce-recomp -O2 -dcore-lint ";

	if ($style eq "h") {
	    $str .= "-fplugin=Language.HERMIT.Plugin " .
                    "-fplugin-opt=Language.HERMIT.Plugin:main:Main/${mod}.hermit ";
	}

	if ($style eq "i") {
	    $str .= "-fplugin=Language.HERMIT.Plugin " .
                    "-fplugin-opt=Language.HERMIT.Plugin:main:Main/- ";
	}

	system($str);
	print "==> $?\n";
	print "running $mod\n";
	system("./${mod}");
	print "==> $?\n";
}

compileAndRun($ARGV[1],$ARGV[0]);




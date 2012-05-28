# hacky tests
#
# Assuming that the HERMIT package has already been install
#

sub compileAndRun {
	my ($style,$mod) = @_;
	print "compiling $mod, using ($style)\n";
	$str = "ghc-7.4.1 ${mod}.hs " .
               "    -fforce-recomp -O2 -dcore-lint -fsimple-list-literals ";

	if ($style eq "h") {
	    $str .= "-fplugin=Language.HERMIT.Plugin " .
                    "-fplugin-opt=Language.HERMIT.Plugin:mode=h " .
                    "-fplugin-opt=Language.HERMIT.Plugin:main:Main/${mod}.hermit ";
	}

	if ($style eq "i") {
	    $str .= "-fplugin=Language.HERMIT.Plugin " .
                    "-fplugin-opt=Language.HERMIT.Plugin:mode=i ";
	}

	if ($style eq "w") {
	    $str .= "-fplugin=Language.HERMIT.Plugin " .
                    "-fplugin-opt=Language.HERMIT.Plugin:mode=w " .
                    "-fplugin-opt=Language.HERMIT.Plugin:testrest.html";
	}

	system($str);
	print "==> $?\n";
	print "running $mod\n";
	system("time ./${mod}");
	print "==> $?\n";
}

compileAndRun($ARGV[1],$ARGV[0]);




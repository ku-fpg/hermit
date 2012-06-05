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
	    $str .= "-fplugin=Language.HERMIT.Plugin.Script " .
                    "-fplugin-opt=Language.HERMIT.Plugin.Script:main:Main:/${mod}.hermit ";
	}

	if ($style eq "i") {
	    $str .= "-fplugin=Language.HERMIT.Plugin.Interactive " .
                    "-fplugin-opt=Language.HERMIT.Plugin.Interactive:main:Main ";
	}

	if ($style eq "w") {
	    $str .= "-fplugin=Language.HERMIT.Plugin.Restful " .
                    "-fplugin-opt=Language.HERMIT.Plugin.Restful:main:Main:testrest.html";
	}

	system($str);
	print "==> $?\n";
	print "running $mod\n";
	system("time ./${mod}");
	print "==> $?\n";
}

compileAndRun($ARGV[1],$ARGV[0]);




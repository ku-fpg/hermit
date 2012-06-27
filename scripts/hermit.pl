#
# Assuming that the HERMIT package has already been install
#

sub compile {
	my ($mod,@opts) = @_;
	print "compiling $mod, using ($mod,@opts)\n";

	$str = "ghc-7.4.1 ${mod} " .
               "    -fforce-recomp -O2 -dcore-lint -fsimple-list-literals ";

	$str .= "-fplugin=HERMIT ";
	foreach (@opts) {
	    $str .= "-fplugin-opt=HERMIT:main:Main:$_ ";
	}
	print "$str\n";

	system($str);
	exit($?);
}

compile(@ARGV);



#
# A very bad Makefile
#

CONTRIB=Coqlib.v Errors.v Integers.v Floats.v AST.v Maps.v Ordered.v \
	 Registers.v

.PHONY: contrib

contrib: /dev/null
	(cd contrib; coqc $(CONTRIB))

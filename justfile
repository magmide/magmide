fullbuild:
	#!/usr/bin/env bash
	pushd theorems
	coq_makefile -f _CoqProject *.v -o Makefile
	make clean
	make
	popd

build:
	#!/usr/bin/env bash
	pushd theorems
	make
	popd

clean:
	#!/usr/bin/env bash
	pushd theorems
	make clean
	rm -f *.glob
	rm -f *.vo
	rm -f *.vok
	rm -f *.vos
	rm -f .*.aux
	rm -f .*.d
	rm -f Makefile*
	popd

# sudo apt install llvm-13
lab:
	lli-13 lab.ll

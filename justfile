# build:
# 	dune build

# wget --no-check-certificate -O - https://apt.llvm.org/llvm-snapshot.gpg.key | sudo apt-key add -
# add-apt-repository 'deb http://apt.llvm.org/bionic/   llvm-toolchain-bionic-13  main'
# sudo apt install llvm-13 libclang-common-13-dev
lab:
	#!/usr/bin/env bash
	# lli-13 lab.ll
	cargo run
	lli-13 lab.bc
	echo $?

test:
	cargo test
	dune runtest

dev:
	cargo test test_parse_type_definition -- --nocapture


clean:
	#!/usr/bin/env bash
	pushd theory
	make clean
	rm -f *.glob
	rm -f *.vo
	rm -f *.vok
	rm -f *.vos
	rm -f .*.aux
	rm -f .*.d
	rm -f Makefile*
	rm -f .lia.cache
	rm -f *.ml*
	popd

build:
	#!/usr/bin/env bash
	pushd theory
	make
	popd

fullbuild:
	#!/usr/bin/env bash
	pushd theory
	coq_makefile -f _CoqProject *.v -o Makefile
	make clean
	make
	popd

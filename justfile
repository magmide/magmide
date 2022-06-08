build:
	dune build

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

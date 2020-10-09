pushd theorems
coq_makefile -f _CoqProject *.v -o Makefile
make clean
make
popd

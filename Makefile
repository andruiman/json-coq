HS_OUTPUT_DIR=../out/coq-hs/

.PHONY: default all clean clean-all

default: CoqMakefile
	mkdir -p ${HS_OUTPUT_DIR}
	make -f CoqMakefile

all: default html

clean: CoqMakefile
	make -f CoqMakefile clean
clean-all: clean
	rm -rf CoqMakefile
	rm -rf CoqMakefile.conf
	-rm -r .*.aux */.*.aux
	-rm -rf ${HS_OUTPUT_DIR}

html: CoqMakefile
	make -f CoqMakefile html
html-no-proofs: CoqMakefile
	make -f CoqMakefile gallinahtml

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

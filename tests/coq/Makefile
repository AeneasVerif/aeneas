ALL_DIRS ?= $(filter-out %.template, $(filter-out Makefile%, $(wildcard *)))

VERIFY_DIRS = $(addprefix verif-,$(ALL_DIRS))

CLEAN_DIRS = $(addprefix clean-,$(ALL_DIRS))

COPY_MAKEFILES = $(addprefix copy-makefile-,$(ALL_DIRS))

GEN_COQ_PROJECT = $(addprefix gen-coq-project-,$(ALL_DIRS))

.PHONY: all
all: $(COPY_MAKEFILES) $(GEN_COQ_PROJECT) $(VERIFY_DIRS)

.PHONY: clean
clean: $(CLEAN_DIRS)

.PHONY: verif-%
verif-%:
	cd $* && make all

.PHONY: copy-makefile-%
copy-makefile-%:
	rm -f $*/Makefile
	echo "# This file was automatically generated - modify ../Makefile.template instead" >> $*/Makefile
	cat Makefile.template >> $*/Makefile

.PHONY: gen-coq-project-%
gen-coq-project-%:
	rm -f $*/_CoqProject
	echo "# This file was automatically generated - see ../Makefile" >> $*/_CoqProject
	cat _CoqProject.template >> $*/_CoqProject
	echo $(patsubst $*/%,"\n"%,$(wildcard $*/*.v)) >> $*/_CoqProject
	sed -i -z "s/ \n/\n/g" $*/_CoqProject

.PHONY: clean-%
clean-%:
	cd $* && make clean

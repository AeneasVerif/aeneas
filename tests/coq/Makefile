ALL_DIRS ?= $(filter-out %.template, $(filter-out Makefile%, $(wildcard *)))

VERIFY_DIRS = $(addprefix verif-,$(ALL_DIRS))

CLEAN_DIRS = $(addprefix clean-,$(ALL_DIRS))

COPY_MAKEFILES = $(addprefix copy-makefile-,$(ALL_DIRS))

GEN_COQ_PROJECT = $(addprefix gen-coq-project-,$(ALL_DIRS))

.PHONY: all
all: prepare-projects verify

.PHONY: prepare-projects
prepare-projects: $(COPY_MAKEFILES) $(GEN_COQ_PROJECT)

.PHONY: verify
verify: $(VERIFY_DIRS)

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
	echo $(wildcard $*/*.v) >> $*/_CoqProject # List the .v files
	sed -i -z "s/"$*"\//\n/g" $*/_CoqProject # Insert breaks
	sed -i -z "s/ \n/\n/g" $*/_CoqProject # Remove whitespaces at the end of lines
	cat $*/_CoqProject

.PHONY: clean
clean: $(CLEAN_DIRS)

.PHONY: clean-%
clean-%:
	cd $* && make clean

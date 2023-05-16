ALL_DIRS ?= $(filter-out %~ Makefile% Holmakefile%, $(wildcard *))

UPDATE_DIRS = $(addprefix update-,$(ALL_DIRS))

VERIFY_DIRS = $(addprefix verif-,$(ALL_DIRS))

CLEAN_DIRS = $(addprefix clean-,$(ALL_DIRS))

COPY_HOLMAKEFILE = $(addprefix copy-holmakefile-,$(ALL_DIRS))

# This allows to customize the INCLUDES variable of the Holmakefile - useful for Nix
HOLMAKEFILE_INCLUDES ?= ../../../backends/hol4

.PHONY: all
all: prepare-projects verify

.PHONY: prepare-projects
prepare-projects: $(COPY_HOLMAKEFILE)

.PHONY: prepare-projects
copy-holmakefile-%:
	rm -f $*/Holmakefile
	echo "# This file was automatically generated - modify ../Holmakefile.template instead" >> $*/Holmakefile
	echo "INCLUDES = " $(HOLMAKEFILE_INCLUDES) >> $*/Holmakefile
	cat Holmakefile.template >> $*/Holmakefile

.PHONY: verify
verify: $(VERIFY_DIRS)

.PHONY: verif-%
verif-%:
	cd $* && Holmake

.PHONY: clean
clean: $(CLEAN_DIRS)

.PHONY: clean-%
clean-%:
	cd $* && Holmake clean

ALL_DIRS ?= $(filter-out %~ Makefile% Holmakefile%, $(wildcard *))

UPDATE_DIRS = $(addprefix update-,$(ALL_DIRS))

VERIFY_DIRS = $(addprefix verif-,$(ALL_DIRS))

CLEAN_DIRS = $(addprefix clean-,$(ALL_DIRS))

COPY_HOLMAKEFILE = $(addprefix copy-holmakefile-,$(ALL_DIRS))

# This allows to customize the INCLUDES variable of the Holmakefile - useful for Nix
AENEAS_PRIMITIVES ?= ../../backends/hol4
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

# There are racing issues with Holmake: if we run several builds in parallel,
# Holmake will complain that the dependencies (in `aeneas/backends/hol4` are
# not built). For this reason, we add this rule which enforces that *one*
# Holmake process builds the dependencies, before the test subdirectories
# (hashmap, etc.) are built in parallel.
.PHONY: verify-primitives
verify-primitives:
	cd $(AENEAS_PRIMITIVES) && Holmake

.PHONY: verify
verify: $(VERIFY_DIRS)

.PHONY: verif-%
verif-%: verify-primitives
	cd $* && Holmake

.PHONY: clean
clean: $(CLEAN_DIRS)

.PHONY: clean-%
clean-%:
	cd $* && Holmake clean

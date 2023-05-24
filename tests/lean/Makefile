ALL_DIRS ?= $(filter-out %~ lean-toolchain% Makefile%, $(wildcard *))

UPDATE_DIRS = $(addprefix update-,$(ALL_DIRS))

VERIFY_DIRS = $(addprefix verif-,$(ALL_DIRS))

CLEAN_DIRS = $(addprefix clean-,$(ALL_DIRS))

COPY_LEAN_TOOLCHAIN = $(addprefix copy-lean-toolchain-,$(ALL_DIRS))

.PHONY: all
all: prepare-projects verify

.PHONY: prepare-projects
prepare-projects: $(COPY_LEAN_TOOLCHAIN)

.PHONY: prepare-projects
copy-lean-toolchain-%:
	cp lean-toolchain $*

.PHONY: update
update: $(UPDATE_DIRS)

.PHONY: update-%
update-%:
	cd $* && lake update

.PHONY: verify
verify: $(VERIFY_DIRS)

.PHONY: verif-%
verif-%:
	cd $* && lake build

.PHONY: clean
clean: $(CLEAN_DIRS)

.PHONY: clean-%
clean-%:
	cd $* && lake clean
